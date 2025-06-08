#!/bin/bash

# make FPGA_PRJ=ucas-cod FPGA_BD=nf OS=phy_os ARCH=riscv32 workload

# 定义各组的benchmark列表
declare -A benchmarks=(
    # ["basic"]="memcpy"
    # ["medium"]="sum mov-c fib add if-else pascal quick-sort select-sort max min3 switch bubble-sort"
    # ["advanced"]="shuixianhua sub-longlong bit recursion fact add-longlong shift wanshu goldbach leap-year prime mul-longlong load-store to-lower-case movsx matrix-mul unalign"
    # ["microbench"]="fib md5 qsort queen sieve ssort 15pz bf dinic"
    ["microbench"]="sieve"
)

# 遍历所有组
for group in "${!benchmarks[@]}"; do
    echo "===== Testing ${group} group ====="
    
    # 遍历组内的每个benchmark
    for bench in ${benchmarks[$group]}; do
        echo "Running benchmark: $bench"
        
        make FPGA_PRJ=ucas-cod FPGA_BD=nf SIM_TARGET=custom_cpu SIM_DUT=riscv32:turbo \
            WORKLOAD="simple_test:${group}:${bench}" bhv_sim_verilator
        
        # 如果需要在失败时停止，取消下面注释
        if [ $? -ne 0 ]; then
            echo "Error occurred, exiting at ${group}:${bench}"
            exit 1
        fi
    done
done

echo "All benchmarks tested!"