#include "div.h"
#include "mul.h"
#include "printf.h"
#include "perf_cnt.h"
#include "trap.h"

#define FRAC_BIT 10

#define RD_ADDR 135106448
#define RD_SIZE_D0 1
#define RD_SIZE_D1 1
#define RD_SIZE_D2 28
#define RD_SIZE_D3 28

#define WEIGHT_ADDR 134217728
#define WEIGHT_SIZE_D0 20
#define WEIGHT_SIZE_D1 1
#define WEIGHT_SIZE_D2 5
#define WEIGHT_SIZE_D3 5

#define WR_ADDR 135108240
#define WR_SIZE_D0 1
#define WR_SIZE_D1 20
#define WR_SIZE_D2 12
#define WR_SIZE_D3 12

#define KERN_ATTR_CONV_PAD 0
#define KERN_ATTR_CONV_STRIDE 1
#define KERN_ATTR_POOL_PAD 0
#define KERN_ATTR_POOL_KERN_SIZE 2
#define KERN_ATTR_POOL_STRIDE 2

// MMIO register address of DNN accelerator
#define GPIO_START_ADDR 0x60030000
#define GPIO_DONE_ADDR 0x60030008

struct size_vec4 {
  unsigned d0;
  unsigned d1;
  unsigned d2;
  unsigned d3;
};

struct mem_addr {
  unsigned rd_addr;
  unsigned weight_addr;
  unsigned wr_addr;
};

int mul(short a, short b) {
#ifndef USE_MUL
  int ans = mul_ll(a, b);
#else
  int ans = a * b;
#endif
  return ans;
}

struct mem_addr addr = {RD_ADDR, WEIGHT_ADDR, WR_ADDR};
struct size_vec4 rd_size = {RD_SIZE_D0, RD_SIZE_D1, RD_SIZE_D2, RD_SIZE_D3};
struct size_vec4 wr_size = {WR_SIZE_D0, WR_SIZE_D1, WR_SIZE_D2, WR_SIZE_D3};
struct size_vec4 weight_size = {WEIGHT_SIZE_D0, WEIGHT_SIZE_D1, WEIGHT_SIZE_D2,
                                WEIGHT_SIZE_D3};
struct size_vec4 conv_size;

extern char _binary_data_result_bin_start[];
extern char _binary_data_result_bin_size[];

void convolution() {
  short *in = (short *)addr.rd_addr;
  short *weight = (short *)addr.weight_addr;
  short *out = (short *)addr.wr_addr;

  unsigned input_fm_w = rd_size.d3;
  unsigned input_fm_h = rd_size.d2;

  unsigned pad = KERN_ATTR_CONV_PAD;
  unsigned pad_len = pad << 1;

  unsigned conv_out_w = rd_size.d3 - weight_size.d3 + pad_len;
  unsigned conv_out_h = rd_size.d2 - weight_size.d2 + pad_len;

  unsigned stride = KERN_ATTR_CONV_STRIDE;

  conv_out_w = div(conv_out_w, stride);
  conv_out_h = div(conv_out_h, stride);

  conv_out_w++;
  conv_out_h++;

  conv_size.d0 = wr_size.d0;
  conv_size.d1 = wr_size.d1;
  conv_size.d2 = conv_out_h;
  conv_size.d3 = conv_out_w;

  // TODO: Please add your implementation here
  int no, ni, y, x, ky, kx;
  int input_size_aligned = mul(RD_SIZE_D2, RD_SIZE_D3);
  int output_size_aligned = mul(conv_out_h, conv_out_w);
  int weight_size_aligned = mul(WEIGHT_SIZE_D2, WEIGHT_SIZE_D3) + 1;

  for (no = 0; no < wr_size.d1; no++) {
    for (ni = 0; ni < rd_size.d1; ni++) {
      int bias_index = mul(weight_size_aligned, no);
      int bias = weight[bias_index];
      for (y = 0; y < conv_out_h; y++) {
        for (x = 0; x < conv_out_w; x++) {
          int sum = 0;
          int output_index =
              mul(no, output_size_aligned) + mul(y, conv_out_w) + x;
          if (ni == 0) {
            out[output_index] = bias;
          }
          for (ky = 0; ky < weight_size.d2; ky++) {
            for (kx = 0; kx < weight_size.d3; kx++) {
              int input_y = mul(y, stride) + ky - pad;
              int input_x = mul(x, stride) + kx - pad;

              if (input_y >= 0 && input_y < input_fm_h && input_x >= 0 &&
                  input_x < input_fm_w) {
                int input_index = mul(ni, input_size_aligned) +
                                  mul(input_y, RD_SIZE_D3) + input_x;
                int weight_index =
                    mul(no, mul(RD_SIZE_D1, weight_size_aligned)) +
                    mul(ni, weight_size_aligned) + mul(ky, WEIGHT_SIZE_D3) +
                    kx + 1;

                sum += mul(in[input_index], weight[weight_index]);
              }
            }
          }
          out[output_index] += sum >> FRAC_BIT;
        }
      }
    }
  }
}

void pooling() {
  short *out = (short *)addr.wr_addr;
  short *in = (short *)addr.wr_addr;

  unsigned output_offset = 0;

  unsigned input_fm_w = conv_size.d3;
  unsigned input_fm_h = conv_size.d2;

  unsigned pad = KERN_ATTR_POOL_PAD;
  unsigned pad_len = pad << 1;

  unsigned pad_w_test = conv_size.d3 - KERN_ATTR_POOL_KERN_SIZE;
  unsigned pad_h_test = conv_size.d2 - KERN_ATTR_POOL_KERN_SIZE;

  unsigned pool_out_w = pad_w_test + pad_len;
  unsigned pool_out_h = pad_h_test + pad_len;

  unsigned stride = KERN_ATTR_POOL_STRIDE;

  unsigned pad_w_test_remain =
      pad_w_test - mul(div(pad_w_test, stride), stride);
  unsigned pad_h_test_remain =
      pad_h_test - mul(div(pad_h_test, stride), stride);

  pool_out_w = div(pool_out_w, stride);
  pool_out_h = div(pool_out_h, stride);
  pool_out_w++;
  pool_out_h++;

  if ((!pad) && (pad_w_test_remain || pad_h_test_remain)) {
    pool_out_w++;
    pool_out_h++;
  }

  // TODO: Please add your implementation here
  int no;
  for (no = 0; no < conv_size.d1; no++) {
    unsigned current_channel_input_base = mul(no, mul(input_fm_h, input_fm_w));
    for (int oy = 0; oy < pool_out_h; oy++) {
      for (int ox = 0; ox < pool_out_w; ox++) {
        short max = -32768;
        for (int ky = 0; ky < KERN_ATTR_POOL_KERN_SIZE; ky++) {
          for (int kx = 0; kx < KERN_ATTR_POOL_KERN_SIZE; kx++) {
            int input_y = mul(oy, stride) + ky - pad;
            int input_x = mul(ox, stride) + kx - pad;

            if (input_y >= 0 && input_y < input_fm_h && input_x >= 0 &&
                input_x < input_fm_w) {
              int input_index = current_channel_input_base +
                                mul(input_y, input_fm_w) + input_x;
              if (in[input_index] > max) {
                max = in[input_index];
              }
            }
          }
        }
        out[output_offset] = max;
        output_offset++;
      }
    }
  }
}

#ifdef USE_HW_ACCEL
void launch_hw_accel() {
  volatile int *gpio_start = (void *)(GPIO_START_ADDR);
  volatile int *gpio_done = (void *)(GPIO_DONE_ADDR);

  // TODO: Please add your implementation here
  *gpio_start |= 0x1;
  while (!（* gpio_done & 0x1)) {
      ; // Wait for the hardware accelerator to finish
    }
}
#endif

int comparing() {
  char *out = (char *)addr.wr_addr;
  char *result = (char *)_binary_data_result_bin_start;

#ifdef USE_HW_ACCEL
  int count = (int)_binary_data_result_bin_size +
              (16 - WR_SIZE_D3) * 2 * WR_SIZE_D2 * WR_SIZE_D1;
#else
  int count = (int)_binary_data_result_bin_size;
#endif

  for (int i = 0, j = 0; i < count; i++) {
#ifdef USE_HW_ACCEL
    int alignment = i & 0x0000001f;
    if (alignment >= (WR_SIZE_D3 << 1))
      continue;
#endif
    if (*(out + i) != *(result + j)) {
      printf("Failed! at address %x and %x with data %x and %x\n", out + i,
             result + j, *(out + i), *(result + j));
      return 1;
    }
    j++;
  }

  printf("Passed!\n");
  return 0;
}

int main() {
  Result res;
  bench_prepare(&res);
#ifdef USE_HW_ACCEL
  printf("Launching task...\n");
  launch_hw_accel();
#else
  printf("starting convolution\n");
  convolution();
  printf("starting pooling\n");
  pooling();
#endif

  bench_done(&res);
  int result = comparing();

  printf("    Cycles:                    %u\n", (unsigned int)res.msec);
  printf("    Retired Instructions:      %u\n", (unsigned int)res.perf_retired_inst_count);
  printf("    Retired Loads:             %u\n", (unsigned int)res.perf_retired_load_count);
  printf("    Retired Stores:            %u\n", (unsigned int)res.perf_retired_store_count);
  printf("    Branches Executed:         %u\n", (unsigned int)res.perf_branch_executed_count);
  printf("    Branches Taken:            %u\n", (unsigned int)res.perf_branch_taken_count);
  printf("    IF Stalls:                 %u\n", (unsigned int)res.perf_if_stall_count);
  printf("    MEM Access Stalls:         %u\n", (unsigned int)res.perf_mem_access_stall_count);
  printf("    IW Stalls:                 %u\n", (unsigned int)res.perf_iw_stall_count);
  printf("    RDW Stalls:                %u\n", (unsigned int)res.perf_rdw_stall_count);
  printf("    Jumps Executed:            %u\n", (unsigned int)res.perf_jump_executed_count);
  printf("    ALU Ops Executed:          %u\n", (unsigned int)res.perf_alu_op_executed_count);
  printf("    Shift Ops Executed:        %u\n", (unsigned int)res.perf_shift_op_executed_count);
  printf("    NOPs in ID:                %u\n", (unsigned int)res.perf_nop_in_id_count);
  printf("    Total MEM Ops Issued:      %u\n", (unsigned int)res.perf_total_mem_ops_count);
  printf("    Register Writes:           %u\n", (unsigned int)res.perf_reg_writes_count);

  printf("benchmark finished\n");

  if (result == 0) {
    hit_good_trap();
  } else {
    nemu_assert(0);
  }

  return 0;
}
