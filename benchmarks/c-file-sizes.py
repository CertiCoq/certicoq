import fnmatch
import os
import re

dearg_string = "_dearg"

flist = fnmatch.filter(os.listdir('.'), "CertiCoq*.c")

flist.sort()

print ("%s, %s, %s, %s, %s" % ("Name", "Dearg name", "Size", "Dearg size", "Diff"))
for f in flist:
    if dearg_string in f:
        size = os.stat(f).st_size
        orig_name = f.replace(dearg_string, "")
        orig_size = os.stat(orig_name).st_size
        res = "%s, %s, %s, %s, %s" % (orig_name, f, orig_size, size, orig_size-size)
        print res
