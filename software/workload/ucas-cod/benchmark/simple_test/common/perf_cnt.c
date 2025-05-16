#include "perf_cnt.h"

// Define base address for performance counters for clarity
#define PERF_CNT_BASE_ADDR 0x60010000UL

// Define offsets for each counter based on the PPT address map
#define PERF_CNT_0_OFFSET  0x0000
#define PERF_CNT_1_OFFSET  0x0008
#define PERF_CNT_2_OFFSET  0x1000
#define PERF_CNT_3_OFFSET  0x1008
#define PERF_CNT_4_OFFSET  0x2000
#define PERF_CNT_5_OFFSET  0x2008
#define PERF_CNT_6_OFFSET  0x3000
#define PERF_CNT_7_OFFSET  0x3008
#define PERF_CNT_8_OFFSET  0x4000
#define PERF_CNT_9_OFFSET  0x4008
#define PERF_CNT_10_OFFSET 0x5000
#define PERF_CNT_11_OFFSET 0x5008
#define PERF_CNT_12_OFFSET 0x6000
#define PERF_CNT_13_OFFSET 0x6008
#define PERF_CNT_14_OFFSET 0x7000
#define PERF_CNT_15_OFFSET 0x7008

// Helper macro to get the full address of a counter
#define PERF_COUNTER_ADDR(offset) (volatile unsigned long *)(PERF_CNT_BASE_ADDR + (offset))

static inline void read_all_perf_counters(Result *res) {
 
    res->perf_retired_inst_count    = *PERF_COUNTER_ADDR(PERF_CNT_1_OFFSET);
    res->perf_retired_load_count    = *PERF_COUNTER_ADDR(PERF_CNT_2_OFFSET);
    res->perf_retired_store_count   = *PERF_COUNTER_ADDR(PERF_CNT_3_OFFSET);
    res->perf_branch_executed_count = *PERF_COUNTER_ADDR(PERF_CNT_4_OFFSET);
    res->perf_branch_taken_count    = *PERF_COUNTER_ADDR(PERF_CNT_5_OFFSET);
    res->perf_if_stall_count        = *PERF_COUNTER_ADDR(PERF_CNT_6_OFFSET);
    res->perf_mem_access_stall_count= *PERF_COUNTER_ADDR(PERF_CNT_7_OFFSET);
    res->perf_iw_stall_count        = *PERF_COUNTER_ADDR(PERF_CNT_8_OFFSET);
    res->perf_rdw_stall_count       = *PERF_COUNTER_ADDR(PERF_CNT_9_OFFSET);
    res->perf_jump_executed_count   = *PERF_COUNTER_ADDR(PERF_CNT_10_OFFSET);
    res->perf_alu_op_executed_count = *PERF_COUNTER_ADDR(PERF_CNT_11_OFFSET);
    res->perf_shift_op_executed_count = *PERF_COUNTER_ADDR(PERF_CNT_12_OFFSET);
    res->perf_nop_in_id_count       = *PERF_COUNTER_ADDR(PERF_CNT_13_OFFSET);
    res->perf_total_mem_ops_count   = *PERF_COUNTER_ADDR(PERF_CNT_14_OFFSET);
    res->perf_reg_writes_count      = *PERF_COUNTER_ADDR(PERF_CNT_15_OFFSET);

}



unsigned long _uptime() {
  // TODO [COD]
  //   You can use this function to access performance counter related with time or cycle.
  volatile unsigned long *cycle_counter_ptr = (volatile unsigned long *)0x60010000;
  return *cycle_counter_ptr;
}

void bench_prepare(Result *res) {
  // TODO [COD]
  //   Add preprocess code, record performance counters' initial states.
  //   You can communicate between bench_prepare() and bench_done() through
  //   static variables or add additional fields in `struct Result`
  res->msec = _uptime();
  read_all_perf_counters(res);
}

void bench_done(Result *res) {
  // TODO [COD]
  //  Add postprocess code, record performance counters' current states.
  res->msec = _uptime() - res->msec;
  Result temp;
  read_all_perf_counters(&temp);
  res->perf_retired_inst_count = temp.perf_retired_inst_count - res->perf_retired_inst_count;
  res->perf_retired_load_count = temp.perf_retired_load_count - res->perf_retired_load_count;
  res->perf_retired_store_count = temp.perf_retired_store_count - res->perf_retired_store_count;
  res->perf_branch_executed_count = temp.perf_branch_executed_count - res->perf_branch_executed_count;
  res->perf_branch_taken_count = temp.perf_branch_taken_count - res->perf_branch_taken_count;
  res->perf_if_stall_count = temp.perf_if_stall_count - res->perf_if_stall_count;
  res->perf_mem_access_stall_count = temp.perf_mem_access_stall_count - res->perf_mem_access_stall_count;
  res->perf_iw_stall_count = temp.perf_iw_stall_count - res->perf_iw_stall_count;
  res->perf_rdw_stall_count = temp.perf_rdw_stall_count - res->perf_rdw_stall_count;
  res->perf_jump_executed_count = temp.perf_jump_executed_count - res->perf_jump_executed_count;
  res->perf_alu_op_executed_count = temp.perf_alu_op_executed_count - res->perf_alu_op_executed_count;
  res->perf_shift_op_executed_count = temp.perf_shift_op_executed_count - res->perf_shift_op_executed_count;
  res->perf_nop_in_id_count = temp.perf_nop_in_id_count - res->perf_nop_in_id_count;
  res->perf_total_mem_ops_count = temp.perf_total_mem_ops_count - res->perf_total_mem_ops_count;
  res->perf_reg_writes_count = temp.perf_reg_writes_count - res->perf_reg_writes_count;
}

