#!/bin/bash

set -e  # Exit immediately if a command exits with a non-zero status.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCHMARK_DIR="${SCRIPT_DIR}/benchmarks"
CWD="${SCRIPT_DIR}"

clean_build() {
    mvn clean package
}

aug_target() {
    local BENCH_TARGET="$1"
    local TARGET_DIR="${BENCHMARK_DIR}/inputs/${BENCH_TARGET}"
    local WORKDIR="${BENCHMARK_DIR}/outputs/${BENCH_TARGET}/checkpoint_datagen"
    # Delete the workdir if it exists
    rm -rf "${WORKDIR}"
    mkdir -p "${WORKDIR}"
    
    cd "${WORKDIR}" || exit
    java -cp "${CWD}/target/classes:${CWD}/libs/*" edu.boisestate.datagen.App -s "${TARGET_DIR}" -w "${WORKDIR}" | tee -a "${WORKDIR}/trace.log"
    if [ ${PIPESTATUS[0]} -ne 0 ]; then
        echo "Java command failed in aug_target" >&2
        exit 1
    fi
}

noaug_target() {
    local BENCH_TARGET="$1"
    local TARGET_DIR="${BENCHMARK_DIR}/inputs/${BENCH_TARGET}"
    local WORKDIR="${BENCHMARK_DIR}/outputs/${BENCH_TARGET}/checkpoint_nodatagen"
    # Delete workdir if exists.
    rm -rf "${WORKDIR}"
    mkdir -p "${WORKDIR}"
    
    cd "${WORKDIR}" || exit
    java -cp "${CWD}/target/classes:${CWD}/libs/*" edu.boisestate.datagen.App -s "${TARGET_DIR}" -w "${WORKDIR}" -k true | tee -a "${WORKDIR}/trace.log"
    if [ ${PIPESTATUS[0]} -ne 0 ]; then
        echo "Java command failed in noaug_target" >&2
        exit 1
    fi
}

run_all() {
    cd "${CWD}" || exit
    clean_build

    noaug_target "$1"

    cd "${CWD}" || exit
    clean_build

    aug_target "$1"

    echo "__________________________________"
    echo "COMPLETED RUNNING TARGETS FOR $1"
    echo "__________________________________"
}

#run_all "A_LT_B"
#run_all "MADWiFi"
#run_all "BindExpandsVars2"
#run_all "DaggerEX1"
#run_all "Ex1"
run_all "TriangleCheck"
run_all "IntDivision"
run_all "Cars"
