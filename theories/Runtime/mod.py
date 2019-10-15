#!/usr/bin/env python
import os, sys

nargs = len(sys.argv)

if not 1 <= nargs <= 3:
    print "usage: %s search_text replace_text [infile [outfile]]" % \
        os.path.basename(sys.argv[0])
else:
    stext1 = "define void"
    rtext1 = "define ghccc void"
    stext2 = "declare void"
    rtext2 = "declare ghccc void"
    stext3 = "call void"
    rtext3 = "call ghccc void"
    stext4 = "define ghccc void @body"
    rtext4 = "define void @body"
    stext5 = "call ghccc void @body"
    rtext5 = "call void @body"
    stext6 = "declare ghccc void @garbage_collect"
    rtext6 = "declare void @garbage_collect"
    stext7 = "call ghccc void @garbage_collect"
    rtext7 = "call void @garbage_collect"
    input = sys.stdin
    output = sys.stdout
    if nargs > 1:
        input = open(sys.argv[1])
    if nargs > 2:
        output = open(sys.argv[2], 'w')
    for s in input.xreadlines(  ):
        output.write(s.replace(stext1, rtext1).replace(stext2, rtext2).replace(stext3, rtext3).replace(stext4, rtext4).replace(stext5, rtext5).replace(stext6, rtext6).replace(stext7, rtext7))
    output.close(  )
    input.close(  )
