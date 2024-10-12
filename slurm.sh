#!/bin/bash
#SBATCH -J BENCHMARKS_SANDESH    # job name
#SBATCH -o log_slurm.out # output and error file name (%j expands to jobID)
#SBATCH -n 48            # total number of tasks requested
#SBATCH -N 1             # number of nodes you want to run on
#SBATCH -p bsudfq        # queue (partition)

# (optional) Print some debugging information
echo "Date              = $(date)"
echo "Hostname          = $(hostname -s)"
echo "Working Directory = $(pwd)"
echo ""
echo "Number of Nodes Allocated  = $SLURM_JOB_NUM_NODES"
echo "Number of Tasks Allocated  = $SLURM_NTASKS"
echo ""

## Run the program
#module load borah-base openmpi/4.1.3/gcc/12.1.0
#mpirun -n 48 ./hello_world
./benchmarks.sh
