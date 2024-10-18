set -e

# Run the noaug targets for a given input name.
INPUTNAME=${1}
CWD=${PWD}

for i in $(seq 1 10)
do 
    DATESTART=$(date +%s)
    ITERATIONS=${ITERATIONS:=2}

    WORKDIR="experiments/${INPUTNAME}/checkpoint_nodatagen/${INPUTNAME}_${DATESTART}"
    mkdir -p ${WORKDIR}
    cd "${WORKDIR}"

    java -cp "${CWD}/libs/*:${CWD}/target/classes/" edu.boisestate.datagen.App -s "${CWD}/benchmarks/inputs/${INPUTNAME}" -w "." -m "${ITERATIONS}" -k true| tee -a "${INPUTNAME}_${DATESTART}_noaug"

    cd -
done