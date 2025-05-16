#include <am.h>
#include <benchmark.h>
#include <trap.h>
#include <limits.h>
#include "perf_cnt.h"

Benchmark *current;
Setting *setting;

static char *start;

#define ARR_SIZE(a) (sizeof((a)) / sizeof((a)[0]))

// The benchmark list

#define ENTRY(_name, _sname, _s1, _s2, _desc) \
  { .prepare = bench_##_name##_prepare, \
    .run = bench_##_name##_run, \
    .validate = bench_##_name##_validate, \
    .name = _sname, \
    .desc = _desc, \
    .settings = {_s1, _s2}, },

Benchmark benchmarks[] = {
  BENCHMARK_LIST(ENTRY)
};

extern char _heap_start[];
extern char _heap_end[];
_Area _heap = {
  .start = _heap_start,
  .end = _heap_end,
};

static const char *bench_check(Benchmark *bench) {
  unsigned long freesp = (unsigned long)_heap.end - (unsigned long)_heap.start;
  if (freesp < setting->mlim) {
    return "(insufficient memory)";
  }
  return NULL;
}

void run_once(Benchmark *b, Result *res) {
  bench_reset();       // reset malloc state
  current->prepare();  // call bechmark's prepare function
  bench_prepare(res);  // clean everything, start timer
  current->run();      // run it
  bench_done(res);     // collect results
  res->pass = current->validate();
}

int main() {
  int pass = 1;

  _Static_assert(ARR_SIZE(benchmarks) > 0, "non benchmark");

  for (int i = 0; i < ARR_SIZE(benchmarks); i++) {
    Benchmark *bench = &benchmarks[i];
    current          = bench;
    setting          = &bench->settings[SETTING];
    const char *msg  = bench_check(bench);
    printk("[%s] %s: ", bench->name, bench->desc);

    if (msg != NULL) {
      printk("Ignored %s\n", msg);
    } else {
      unsigned long best_msec                         = ULONG_MAX;
      int succ                                        = 1;

      unsigned long best_perf_retired_inst_count    = 0;
      unsigned long best_perf_retired_load_count    = 0;
      unsigned long best_perf_retired_store_count   = 0;
      unsigned long best_perf_branch_executed_count = 0;
      unsigned long best_perf_branch_taken_count    = 0;
      unsigned long best_perf_if_stall_count        = 0;
      unsigned long best_perf_mem_access_stall_count= 0;
      unsigned long best_perf_iw_stall_count        = 0;
      unsigned long best_perf_rdw_stall_count       = 0;
      unsigned long best_perf_jump_executed_count   = 0;
      unsigned long best_perf_alu_op_executed_count = 0;
      unsigned long best_perf_shift_op_executed_count = 0;
      unsigned long best_perf_nop_in_id_count       = 0;
      unsigned long best_perf_total_mem_ops_count   = 0;
      unsigned long best_perf_reg_writes_count      = 0;

      for (int r = 0; r < REPEAT; r++) {
        Result current_run_res;
        run_once(bench, &current_run_res);

        printk(current_run_res.pass ? "*" : "X");
        succ &= current_run_res.pass;

        if (current_run_res.msec < best_msec) {
          best_msec                         = current_run_res.msec;
          best_perf_retired_inst_count    = current_run_res.perf_retired_inst_count;
          best_perf_retired_load_count    = current_run_res.perf_retired_load_count;
          best_perf_retired_store_count   = current_run_res.perf_retired_store_count;
          best_perf_branch_executed_count = current_run_res.perf_branch_executed_count;
          best_perf_branch_taken_count    = current_run_res.perf_branch_taken_count;
          best_perf_if_stall_count        = current_run_res.perf_if_stall_count;
          best_perf_mem_access_stall_count= current_run_res.perf_mem_access_stall_count;
          best_perf_iw_stall_count        = current_run_res.perf_iw_stall_count;
          best_perf_rdw_stall_count       = current_run_res.perf_rdw_stall_count;
          best_perf_jump_executed_count   = current_run_res.perf_jump_executed_count;
          best_perf_alu_op_executed_count = current_run_res.perf_alu_op_executed_count;
          best_perf_shift_op_executed_count = current_run_res.perf_shift_op_executed_count;
          best_perf_nop_in_id_count       = current_run_res.perf_nop_in_id_count;
          best_perf_total_mem_ops_count   = current_run_res.perf_total_mem_ops_count;
          best_perf_reg_writes_count      = current_run_res.perf_reg_writes_count;
        }
      }

      if (succ) {
        printk(" Passed.\n");
      } else {
        printk(" Failed.\n");
      }
      pass &= succ;

      if (succ && best_msec != ULONG_MAX) {
          printk("  --- Performance Counters for [%s] (Best Cycle Run Deltas) ---\n", bench->name);
          printk("    Cycles           :         %u\n", (unsigned int)best_msec);
          printk("    Retired Instructions:      %u\n", (unsigned int)best_perf_retired_inst_count);
          printk("    Retired Loads:             %u\n", (unsigned int)best_perf_retired_load_count);
          printk("    Retired Stores:            %u\n", (unsigned int)best_perf_retired_store_count);
          printk("    Branches Executed:         %u\n", (unsigned int)best_perf_branch_executed_count);
          printk("    Branches Taken:            %u\n", (unsigned int)best_perf_branch_taken_count);
          printk("    IF Stalls:                 %u\n", (unsigned int)best_perf_if_stall_count);
          printk("    MEM Access Stalls:         %u\n", (unsigned int)best_perf_mem_access_stall_count);
          printk("    IW Stalls:                 %u\n", (unsigned int)best_perf_iw_stall_count);
          printk("    RDW Stalls:                %u\n", (unsigned int)best_perf_rdw_stall_count);
          printk("    Jumps Executed:            %u\n", (unsigned int)best_perf_jump_executed_count);
          printk("    ALU Ops Executed:          %u\n", (unsigned int)best_perf_alu_op_executed_count);
          printk("    Shift Ops Executed:        %u\n", (unsigned int)best_perf_shift_op_executed_count);
          printk("    NOPs in ID:                %u\n", (unsigned int)best_perf_nop_in_id_count);
          printk("    Total MEM Ops Issued:      %u\n", (unsigned int)best_perf_total_mem_ops_count);
          printk("    Register Writes:           %u\n", (unsigned int)best_perf_reg_writes_count);
          printk("  --- End of Counters for [%s] ---\n", bench->name);
      } else if (succ) {
          printk("  --- No performance data to display for [%s] (no runs completed with data) ---\n", bench->name);
      }
    }
  }

  printk("benchmark finished\n");

  if(pass)
      hit_good_trap();
  else
      nemu_assert(0);

  return 0;
}

// Library


void* bench_alloc(size_t size) {
  if ((uintptr_t)start % 16 != 0) {
    start = start + 16 - ((uintptr_t)start % 16);
  }
  char *old = start;
  start += size;
  assert((uintptr_t)_heap.start <= (uintptr_t)start && (uintptr_t)start < (uintptr_t)_heap.end);
  for (char *p = old; p != start; p ++) *p = '\0';
  assert((uintptr_t)start - (uintptr_t)_heap.start <= setting->mlim);
  return old;
}

void bench_free(void *ptr) {
}

void bench_reset() {
  start = (char*)_heap.start;
}

static int32_t seed = 1;

void bench_srand(int32_t _seed) {
  seed = _seed & 0x7fff;
}

int32_t bench_rand() {
  seed = (mmul_u(seed , (int32_t)214013L) + (int32_t)2531011L);
  return (seed >> 16) & 0x7fff;
}

// FNV hash
uint32_t checksum(void *start, void *end) {
  const int32_t x = 16777619;
  int32_t hash = 2166136261u;
  for (uint8_t *p = (uint8_t*)start; p + 4 < (uint8_t*)end; p += 4) {
    int32_t h1 = hash;
    for (int i = 0; i < 4; i ++) {
      h1 = mmul_u((h1 ^ p[i]) , x);
    }
    hash = h1;
  }
  hash += hash << 13;
  hash ^= hash >> 7;
  hash += hash << 3;
  hash ^= hash >> 17;
  hash += hash << 5;
  return hash;
}

