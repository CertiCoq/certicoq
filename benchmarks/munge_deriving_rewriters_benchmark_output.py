try:
    import sys
    with open(sys.argv[1]) as f:
        lines = f.readlines()
except:
    print('Usage: python3 _.py <file containing output data to munge>')
    exit()

def split_on(f, xss):
    nonempty = False
    xs = []
    for x in xss:
        if f(x):
            yield xs
            nonempty = True
            xs = []
        else:
            xs.append(x)
    if nonempty or xs:
        yield xs

def is_run_divider(s): return s.startswith('-'*20 + ' ')
def is_config_divider(s): return s.startswith('-'*10 + ' ')
def is_prog_divider(s): return not s.startswith('Debug')
def strip_nil(ss): return filter(lambda s: len(s) > 0, ss)

def parse_time_elapsed(msg): return float(msg.split(':')[2].strip())

def parse_debug_msgs_for_one_compilation_unit(msgs):
    shrink_time = None
    uncurry_time = None
    for msg in msgs:
        if 'shrink' in msg.lower():
            shrink_time = parse_time_elapsed(msg)
        elif 'Uncurry' in msg:
            uncurry_time = parse_time_elapsed(msg)
            break
    return {
        'shrink_time': shrink_time,
        'uncurry_time': uncurry_time,
    }

def parse_debug_msgs(msgs):
    vs_easy, vs_hard, binom, color, sha = tuple(
        parse_debug_msgs_for_one_compilation_unit(msgs)
        for msgs in strip_nil(split_on(is_prog_divider, msgs))
    )
    return {
        'vs_easy': vs_easy,
        'vs_hard': vs_hard,
        'binom': binom,
        'color': color,
        'sha': sha,
    }

def parse_run(run):
    manual, shrink, uncurry = tuple(
        parse_debug_msgs(s)
        for s in strip_nil(split_on(is_config_divider, run))
    )
    return {
        'manual': manual,
        'shrink_proto': shrink,
        'uncurry_proto': uncurry,
    }

def parse(lines):
    return [
        parse_run(run)
        for run in strip_nil(split_on(is_run_divider, lines))
    ]

def analyze_with(f, data):
    res = dict()
    for k, v in data[0].items():
        res[k] = f([d[k] for d in data])
    return res

def analyze_opt_pass(data):
    from statistics import mean, stdev
    return {'mean': mean(data)*1000, 'stdev': stdev(data)*1000}
def analyze_unit(data): return analyze_with(analyze_opt_pass, data)
def analyze_config(data): return analyze_with(analyze_unit, data)
def analyze(data): return analyze_with(analyze_config, data)

def dict_map(d, f): return dict((k, f(v)) for k, v in d.items())
def keep_time(name, data):
    return dict(
        (prog, times[name])
        for prog, times in data.items()
    )

data = analyze(parse(lines))
manual_shrink = keep_time('shrink_time', data['manual'])
manual_uncurry = keep_time('uncurry_time', data['manual'])
tool_shrink = keep_time('shrink_time', data['shrink_proto'])
tool_uncurry = keep_time('uncurry_time', data['uncurry_proto'])

def latex_of_stats(manual_stats, auto_stats):
    def escape_for_latex(s): return s.replace('_', '\\_')
    return '\n'.join(
        f"{escape_for_latex(prog)} & " +
        f"{manual_times['mean']:.2f} $\\pm$ {manual_times['stdev']:.2f} & " +
        f"{auto_stats[prog]['mean']:.2f} $\\pm$ {auto_stats[prog]['stdev']:.2f} \\\\\\hline"
        for prog, manual_times in manual_stats.items()
    )

print('-------------------- shrink --------------------')
print(latex_of_stats(manual_shrink, tool_shrink))
print('-------------------- uncurry --------------------')
print(latex_of_stats(manual_uncurry, tool_uncurry))
