"""
This is a super simple script that runs the benchmarking for the project.

The benchmarks follow the following structure:
- benchmarks/inputs/<benchmark_name>/[benchmark_name.java, benchmark_name.expected]
- benchmarks/outputs/<benchmark_name>/[checkpoint_datagen/, checkpoint_nodatagen/, trace.log]/
"""

import os
import threading
import glob
import subprocess

benchmarks = os.listdir("benchmarks/inputs")
benchmarks = [x for x in benchmarks if os.path.isdir(f"benchmarks/inputs/{x}")]

# Delete existing folders in outputs folder.
os.system("rm -rf benchmarks/outputs/*")

# Generate output folders for each benchmark.
for benchmark in benchmarks:
    os.system(f"mkdir -p benchmarks/outputs/{benchmark}/checkpoint_datagen")
    os.system(f"mkdir -p benchmarks/outputs/{benchmark}/checkpoint_nodatagen")


# Run the benchmark using our current java project.
def run_datagen_benchmark(benchmark_name: str):
    for i in range(0, 1000):
        import time

        time.sleep(0.1)
        print(i)
    ...


def run_nodatagen_benchmark(benchmark_name: str): ...


benchmark_folder = "benchmarks"

# Build the project first.
print("Building the project first.")
command = "mvn clean package"
process = subprocess.Popen(command.split(), stdout=subprocess.PIPE)
process.wait()
print("Building done. Now running the benchmarks.")


def benchmark_runner(benchmark):
    # classpaths for our thing.
    classpaths = []
    # first of all, the target/classes classpath.
    classpaths.append(f"{os.getcwd()}/target/classes")
    # then, the benchmark source folder.
    classpaths.append(f"benchmarks/inputs/{benchmark}")
    # then, the lib folder.
    mypath = os.getcwd()
    classpaths.append(":".join(glob.glob(f"{mypath}/libs/*.jar")))

    print("Running DATAGEN benchmark:", benchmark)

    # then, depending on the datagenoutput folder,
    # we might need to add the datagen output folder.
    classpaths.append(f"benchmarks/outputs/{benchmark}/checkpoint_datagen")
    classpaths = ":".join(classpaths)
    
    checkpointdir = f"{mypath}/{benchmark_folder}/outputs/{benchmark}/checkpoint_datagen"

    # datagen
    command = [
        "java",
        "-cp",
        f"/Users/sandesh/Workspace/thesis/javaparser/my-app/target/classes:benchmarks/inputs/A_LT_B:{classpaths}:benchmarks/outputs/{benchmark}/checkpoint_datagen",
        "edu.boisestate.datagen.App",
        "-s",
        f"{mypath}/{benchmark_folder}/inputs/{benchmark}/",
        "-w",
        checkpointdir
    ]

    with open(f"{mypath}/{benchmark_folder}/outputs/{benchmark}/trace_datagen.log", "w") as f:
        process = subprocess.Popen(
            command,
            cwd=checkpointdir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        for line in process.stdout:
            print(line, end="")
            f.write(line)
            f.flush()

        for stderr_line in process.stderr:
            print(stderr_line, end="")  # Print stderr to console
            f.write(stderr_line)  # Write stderr to file
            f.flush()  # Flush to file

        process.wait()
        
    # no datagen.
    print("Running NODATAGEN benchmark:", benchmark)
    command = [
        "java",
        "-cp",
        f"/Users/sandesh/Workspace/thesis/javaparser/my-app/target/classes:benchmarks/inputs/A_LT_B:{classpaths}:benchmarks/outputs/{benchmark}/checkpoint_nodatagen",
        "edu.boisestate.App",
        "-s",
        f"{mypath}/{benchmark_folder}/inputs/{benchmark}/",
        "-w",
        f"{mypath}/{benchmark_folder}/outputs/{benchmark}/checkpoint_nodatagen",
        "-k",
        "true"
    ]
    
    print(' '.join(command))
    checkpointdir = f"{mypath}/{benchmark_folder}/outputs/{benchmark}/checkpoint_nodatagen" 
    with open(f"{mypath}/{benchmark_folder}/outputs/{benchmark}/trace_nodatagen.log", "w") as f:
        process = subprocess.Popen(
            command,
            cwd=checkpointdir,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        for line in process.stdout:
            print(line, end="")
            f.write(line)
            f.flush()

        for stderr_line in process.stderr:
            print(stderr_line, end="")
            f.write(stderr_line)
            f.flush()
            
        process.wait()
        
    print("Finished running benchmarks for ", benchmark)

threads = []
# Run all benchmarks in parallel.
for benchmark in benchmarks:
    # run benchmark.
    # Run a thread for each benchmark.
    thread = threading.Thread(target=benchmark_runner, args=(benchmark,))
    thread.start()
    threads.append(thread)

# join all threads.
for thread in threads:
    thread.join()