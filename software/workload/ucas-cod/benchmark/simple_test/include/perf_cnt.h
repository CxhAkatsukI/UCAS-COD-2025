#ifndef __PERF_CNT__
#define __PERF_CNT__

#ifdef __cplusplus
extern "C" {
#endif

typedef struct Result {
    int pass;                 // Whether the benchmark passed or failed
    unsigned long msec;       // Typically used for cycle count of the benchmark run (cpu_perf_cnt_0)

    unsigned long perf_retired_inst_count;    // From cpu_perf_cnt_1
    unsigned long perf_retired_load_count;    // From cpu_perf_cnt_2
    unsigned long perf_retired_store_count;   // From cpu_perf_cnt_3
    unsigned long perf_branch_executed_count; // From cpu_perf_cnt_4
    unsigned long perf_branch_taken_count;    // From cpu_perf_cnt_5
    unsigned long perf_if_stall_count;        // From cpu_perf_cnt_6
    unsigned long perf_mem_access_stall_count;// From cpu_perf_cnt_7
    unsigned long perf_iw_stall_count;        // From cpu_perf_cnt_8
    unsigned long perf_rdw_stall_count;       // From cpu_perf_cnt_9
    unsigned long perf_jump_executed_count;   // From cpu_perf_cnt_10
    unsigned long perf_alu_op_executed_count; // From cpu_perf_cnt_11
    unsigned long perf_shift_op_executed_count; // From cpu_perf_cnt_12
    unsigned long perf_nop_in_id_count;       // From cpu_perf_cnt_13
    unsigned long perf_total_mem_ops_count;   // From cpu_perf_cnt_14
    unsigned long perf_reg_writes_count;      // From cpu_perf_cnt_15

} Result;

void bench_prepare(Result *res);
void bench_done(Result *res);

#endif
