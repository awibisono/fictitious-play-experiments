import resource, subprocess, time, json, sys
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
start=time.monotonic()
command=[sys.executable,'exact_events.py','--orders','3','--events','2000000','--seconds','300','--logt','1000']
with open('run.log','w') as log:
 p=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,timeout=420)
u=resource.getrusage(resource.RUSAGE_CHILDREN)
Path('resource.json').write_text(json.dumps(dict(command=command,exit_code=p.returncode,elapsed_seconds=time.monotonic()-start,max_rss_kib=u.ru_maxrss,user_seconds=u.ru_utime,system_seconds=u.ru_stime,address_space_limit_bytes=2*1024**3),indent=2)+'\n')
sys.exit(p.returncode)
