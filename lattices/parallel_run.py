import sys
import time
from genus import write_all_of_sig_between_genera_basic
# switching from multiprocessing to parallel
#import multiprocessing
#from multiprocessing import Pool
#from functools import reduce

min_rank = 1
max_rank = 32
# num_cpus = 128 # change this according to platform
C = 32768
batch_size = 128
ranks = range(min_rank,max_rank+1) 

#tasks = []
inputs = []

for r in ranks:
    sigs = [(r - n_minus, n_minus) for n_minus in range(r//2+1)]
    max_det = C // r
    for sig in sigs:
        if (12 <= r) and (r <= 20) and (sig[1] in [1,2]):
            max_det = C // (22 - r)
        intervals = range(1,max_det+1,(max_det+1) // batch_size + 1)
        #tasks_sig = [(write_all_of_sig_between_genera_basic, (sig[0], sig[1], intervals[i], intervals[i+1])) for i in range(batch_size)]
        #tasks.append(tasks_sig)
        inputs_sig = [(sig[0], sig[1], intervals[i]+1, intervals[i+1]) for i in range(batch_size)]
        inputs.append(inputs_sig)

all_inputs = reduce(lambda x,y : x+y, inputs)
total = len(all_inputs)
start_time = time.time()

print(f"Starting {total} tasks...")

results = []
for i, res in enumerate(write_all_of_sig_between_genera_basic(inputs), 1):
    results.append(res)
    
    # Calculate progress and ETA
    elapsed = time.time() - start_time
    avg_time = elapsed / i
    eta = avg_time * (total - i)
    percent = (i / total) * 100
    
    # Build the bar string
    bar = "#" * int(percent // 5) + "-" * (20 - int(percent // 5))
    
    # Update the same line in stdout
    sys.stdout.write(f"\r|{bar}| {percent:.1f}% ({i}/{total}) | ETA: {eta:.1f}s")
    sys.stdout.flush()

print("\nDone!")

#def calculate(func, args):
#    result = func(*args)
#    return '%s says that %s%s = %s' % (
#        multiprocessing.current_process().name,
#        func.__name__, args, result
        )

#all_tasks = reduce(lambda x,y : x + y, tasks)
#my_pool = Pool(num_cpus)
#results = [my_pool.apply_async(calculate, t) for t in all_tasks]
#ndone = sum([res.ready() for res in results])
#while (ndone < len(results)):
#     sleep(5)
#     ndone = sum([res.ready() for res in results])
#     print("done/njobs = ", ndone, "/", len(results))
#my_pool.close()