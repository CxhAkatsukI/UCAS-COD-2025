#include "div.h"
#include "mul.h"
#include "perf_cnt.h"
#include "printf.h"
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

// =================================================================================================
//                                  Convolution Function
// =================================================================================================
// Performs a 2D convolution operation on the input feature maps using specified weights and biases.
// The input and weight data are shorts, representing fixed-point numbers.
// The output is also short, after accumulation, bias addition, and quantization (right shift).
//
// Parameters:
//   Implicitly uses global structs:
//     - `addr`: Contains memory addresses for input, weights, and output.
//     - `rd_size`: Dimensions of the input data (N, Ci, Hi, Wi).
//     - `weight_size`: Dimensions of the weight data (Co, Ci_kernel, Hk, Wk).
//                       (Ci_kernel is assumed to be rd_size.d1)
//     - `wr_size`: Expected dimensions of the output data (N, Co, Ho, Wo).
//                  Actual Ho, Wo are calculated by this function.
//     - `conv_size`: Stores the calculated output dimensions for use by subsequent layers (e.g., pooling).
//
// Defines used:
//   - `KERN_ATTR_CONV_PAD`: Padding pixels for convolution.
//   - `KERN_ATTR_CONV_STRIDE`: Stride for convolution.
//   - `FRAC_BIT`: Number of fractional bits for fixed-point quantization.
//
// Assumed Weight Layout:
//   For each output channel (filter): [bias, kernel_weights_for_input_channel_0, kernel_weights_for_input_channel_1, ...]
//   Since RD_SIZE_D1 (input channels) is 1 in this specific configuration, it simplifies to:
//   [bias_filter0, kernel_weights_filter0_for_input0,
//    bias_filter1, kernel_weights_filter1_for_input0,
//    ...]
//   The '+1' in weight_index calculation correctly skips the bias when accessing kernel elements.
// =================================================================================================
void convolution() {
    // --- Pointer Initialization ---
    // Obtain direct pointers to the memory regions for input, weights, and output.
    short *in     = (short *)addr.rd_addr;
    short *weight = (short *)addr.weight_addr;
    short *out    = (short *)addr.wr_addr;

    // --- Input Feature Map Dimensions ---
    unsigned input_fm_w = rd_size.d3; // Width of input feature map
    unsigned input_fm_h = rd_size.d2; // Height of input feature map

    // --- Convolution Parameters ---
    unsigned pad      = KERN_ATTR_CONV_PAD;   // Padding size
    unsigned pad_len  = pad << 1;             // Total padding added to width/height (pad_top + pad_bottom or pad_left + pad_right)
    unsigned stride   = KERN_ATTR_CONV_STRIDE;// Convolution stride

    // --- Output Dimensions Calculation ---
    // Calculate the dimensions of the output feature map based on input size, kernel size, padding, and stride.
    unsigned conv_out_w = rd_size.d3 - weight_size.d3 + pad_len; // Output width before striding
    unsigned conv_out_h = rd_size.d2 - weight_size.d2 + pad_len; // Output height before striding

    conv_out_w = div(conv_out_w, stride); // Apply stride to width
    conv_out_h = div(conv_out_h, stride); // Apply stride to height

    conv_out_w++; // Standard formula for output size often includes a +1 after division by stride
    conv_out_h++; // (e.g., floor((Input + 2*Pad - Kernel) / Stride) + 1)

    // --- Store Calculated Convolution Output Size ---
    // These dimensions will be used by subsequent layers (e.g., pooling).
    conv_size.d0 = wr_size.d0;     // Batch size (N)
    conv_size.d1 = wr_size.d1;     // Number of output channels (Co)
    conv_size.d2 = conv_out_h;     // Calculated output height (Ho)
    conv_size.d3 = conv_out_w;     // Calculated output width (Wo)

    // --- Loop Variables and Pre-calculated Sizes/Offsets for Optimization ---
    int no, ni, y, x, ky, kx; // Loop iterators

    // Pre-calculate sizes of feature maps and weight blocks to reduce `mul` calls within loops.
    // These represent the number of elements (shorts) in the respective dimensions.
    int input_size_aligned  = mul(RD_SIZE_D2, RD_SIZE_D3);        // Total elements in one input feature map (Hi * Wi)
    int output_size_aligned = mul(conv_out_h, conv_out_w);        // Total elements in one output feature map (Ho * Wo)
    int weight_size_aligned = mul(WEIGHT_SIZE_D2, WEIGHT_SIZE_D3) + 1; // Elements in one kernel (Hk * Wk) + 1 for bias
    int weight_size_grouped = mul(weight_size_aligned, RD_SIZE_D1);    // Total elements for one output filter's weights across all its input channels.
                                                                       // Since RD_SIZE_D1 is 1, this equals weight_size_aligned.

    // Offsets for iterating through multi-dimensional arrays in a flattened 1D memory layout.
    // These are progressively updated using strength reduction (addition instead of repeated multiplication).
    int bias_index         = 0; // Index to fetch the current bias value from the weight array.
    int output_no_offset   = 0; // Base offset for the current output feature map (channel `no`).
    int output_y_offset    = 0; // Offset for the current row `y` within the current output feature map.
    int input_ni_offset    = 0; // Base offset for the current input feature map (channel `ni`).
    int weight_no_offset   = 0; // Base offset for the weights of the current output filter (`no`).
    int weight_ni_offset   = 0; // Offset for the weights corresponding to input channel `ni` for the current filter.
    int y_stride           = 0; // Accumulates `y * stride` for calculating input coordinates.
    int x_stride           = 0; // Accumulates `x * stride` for calculating input coordinates.

    // --- Convolution Main Loops ---
    // Iterate over each output channel (filter).
    // `wr_size.d1` is the number of output channels (Co).
    for (no = 0; no < wr_size.d1; no++) {
        // Fetch the bias for the current output channel `no`.
        // Assumes biases are stored at the beginning of each filter's weight block.
        int bias = weight[bias_index];

        // Reset offsets for input channel and corresponding weights for the new output filter.
        // Since RD_SIZE_D1 (input channels) is 1, `ni` loop will only run for `ni = 0`.
        input_ni_offset  = 0;
        weight_ni_offset = 0;

        // Iterate over each input channel.
        // `rd_size.d1` is the number of input channels (Ci).
        // For this specific configuration, RD_SIZE_D1 = 1, so this loop executes only once (ni=0).
        for (ni = 0; ni < rd_size.d1; ni++) {
            // Reset offsets for the current output row `y` and its corresponding strided input coordinate.
            output_y_offset = 0;
            y_stride        = 0;

            // Iterate over the height of the output feature map.
            for (y = 0; y < conv_out_h; y++) {
                // Reset offset for the current output column `x` and its corresponding strided input coordinate.
                x_stride = 0;

                // Iterate over the width of the output feature map.
                for (x = 0; x < conv_out_w; x++) {
                    // Accumulator for the sum of products for the current output pixel.
                    int sum = 0;

                    // Calculate the flattened 1D index for the current output pixel.
                    int output_index = output_no_offset + output_y_offset + x;

                    // Initialize the output pixel with the bias value.
                    // This happens only for the first input channel's contribution (ni=0).
                    // Since RD_SIZE_D1 = 1, this condition is always met.
                    if (ni == 0) {
                        out[output_index] = bias;
                    }

                    // Perform the 2D convolution (multiply-accumulate) for the current output pixel.
                    // Iterate over the height of the convolution kernel.
                    for (ky = 0; ky < weight_size.d2; ky++) {
                        // Calculate the y-coordinate in the input feature map.
                        int input_y = y_stride + ky - pad;
                        // Pre-calculate row offsets for input and weight matrices to reduce `mul` in the innermost loop.
                        int input_input_y_offset  = mul(RD_SIZE_D3, input_y);  // Offset for row `input_y` in input FM.
                        int weight_input_y_offset = mul(WEIGHT_SIZE_D3, ky);   // Offset for row `ky` in the kernel.

                        // Iterate over the width of the convolution kernel.
                        for (kx = 0; kx < weight_size.d3; kx++) {
                            // Calculate the x-coordinate in the input feature map.
                            int input_x = x_stride + kx - pad;

                            // Boundary check: Ensure the current input pixel (input_y, input_x) is within valid bounds.
                            if (input_y >= 0 && input_y < input_fm_h && input_x >= 0 &&
                                input_x < input_fm_w) {
                                // Calculate the flattened 1D index for the current input pixel.
                                int input_index =
                                    input_ni_offset + input_input_y_offset + input_x;
                                // Calculate the flattened 1D index for the current weight kernel element.
                                // The `+ 1` is crucial to skip the bias value stored at the beginning of the weight block.
                                int weight_index = weight_no_offset + weight_ni_offset +
                                                   weight_input_y_offset + kx + 1;

                                // Multiply input pixel by kernel weight and add to sum.
                                sum += mul(in[input_index], weight[weight_index]);
                            }
                        } // End kernel width loop (kx)
                    } // End kernel height loop (ky)

                    // Update `x_stride` for the next output pixel in the row (strength reduction).
                    x_stride += stride;
                    // Add the quantized sum to the (bias-initialized) output pixel.
                    // `sum >> FRAC_BIT` performs fixed-point quantization.
                    out[output_index] += sum >> FRAC_BIT;

                } // End output width loop (x)

                // Update offsets for the next row in the output feature map (strength reduction).
                output_y_offset += conv_out_w;
                y_stride        += stride;

            } // End output height loop (y)

            // Update offsets for the next input channel (strength reduction).
            // These are inside the `ni` loop, but since `ni` only iterates once,
            // they effectively update once per `no` iteration.
            input_ni_offset  += input_size_aligned;
            weight_ni_offset += weight_size_aligned;

        } // End input channel loop (ni)

        // Update base offsets for the next output channel/filter (strength reduction).
        bias_index         += weight_size_aligned; // Move to the bias of the next filter.
        output_no_offset   += output_size_aligned; // Move to the start of the next output feature map.
        weight_no_offset   += weight_size_grouped; // Move to the start of the next filter's weight block.

    } // End output channel loop (no)
}


// =================================================================================================
//                                     Pooling Function
// =================================================================================================
// Performs a 2D max pooling operation on the input feature maps (typically output from convolution).
// The input data is short, and the output is also short, representing the maximum value
// within each pooling window.
//
// Parameters:
//   Implicitly uses global structs:
//     - `addr`: Contains memory addresses. Input for pooling is `addr.wr_addr` (conv output),
//               and output of pooling is also written to `addr.wr_addr` (in-place or flattened).
//     - `conv_size`: Dimensions of the input data to pooling (output of convolution).
//
// Defines used:
//   - `KERN_ATTR_POOL_PAD`: Padding pixels for pooling.
//   - `KERN_ATTR_POOL_KERN_SIZE`: Size (height and width) of the pooling kernel.
//   - `KERN_ATTR_POOL_STRIDE`: Stride for pooling.
// =================================================================================================
void pooling() {
    // --- Pointer Initialization ---
    // Input to pooling is the output of the convolution layer.
    // Output of pooling is written to the same memory region (or a new one if `output_offset` implies flattening to a different structure).
    short *out = (short *)addr.wr_addr; // Output pointer
    short *in  = (short *)addr.wr_addr; // Input pointer (convolution output)

    // --- Global Output Offset ---
    // `output_offset` tracks the flattened 1D index for writing pooled results.
    // This implies the pooled output is a contiguous block of memory, regardless of its 4D structure.
    unsigned output_offset = 0;

    // --- Input Feature Map Dimensions (from convolution output) ---
    unsigned input_fm_w = conv_size.d3; // Width of input feature map to pooling
    unsigned input_fm_h = conv_size.d2; // Height of input feature map to pooling

    // --- Pooling Parameters ---
    unsigned pad         = KERN_ATTR_POOL_PAD;        // Padding size
    unsigned pad_len     = pad << 1;                  // Total padding (if used, though typically 0 for pooling)
    unsigned kernel_size = KERN_ATTR_POOL_KERN_SIZE;  // Pooling kernel window size (assumed square)
    unsigned stride      = KERN_ATTR_POOL_STRIDE;     // Pooling stride

    // --- Output Dimensions Calculation for Pooling ---
    // Calculate the dimensions of the feature map after pooling.
    unsigned pad_w_test = conv_size.d3 - kernel_size; // Effective width for pooling window start positions
    unsigned pad_h_test = conv_size.d2 - kernel_size; // Effective height for pooling window start positions

    unsigned pool_out_w = pad_w_test + pad_len; // Output width before striding
    unsigned pool_out_h = pad_h_test + pad_len; // Output height before striding

    // Calculate remaining pixels if input size is not perfectly divisible by stride after considering kernel.
    // This logic is specific to how "incomplete" pooling windows at the edges are handled.
    unsigned pad_w_test_remain =
        pad_w_test - mul(div(pad_w_test, stride), stride);
    unsigned pad_h_test_remain =
        pad_h_test - mul(div(pad_h_test, stride), stride);

    pool_out_w = div(pool_out_w, stride); // Apply stride to width
    pool_out_h = div(pool_out_h, stride); // Apply stride to height
    pool_out_w++; // Standard formula for output size
    pool_out_h++;

    // Adjust output size if no padding is used and there are remaining elements
    // that would form an incomplete window but are still processed (common for "valid" style pooling edge cases).
    if ((!pad) && (pad_w_test_remain || pad_h_test_remain)) {
        pool_out_w++;
        pool_out_h++;
    }

    // --- Loop Variables and Offsets for Optimization ---
    int no; // Iterator for feature maps (channels)

    // Offsets for iterating through multi-dimensional arrays, updated using strength reduction.
    int oy_offset      = 0; // Accumulates `oy * stride` for calculating input y-coordinates for pooling window.
    int ox_offset      = 0; // Accumulates `ox * stride` for calculating input x-coordinates for pooling window.
    int input_y_offset = 0; // Stores `input_y * input_fm_w` for current input row.

    // --- Pooling Main Loops ---
    // Iterate over each feature map (channel).
    // `conv_size.d1` is the number of channels from the convolution output.
    for (no = 0; no < conv_size.d1; no++) {
        // Calculate the base address/offset for the current input feature map.
        // `mul(input_fm_h, input_fm_w)` is the size of one complete 2D feature map.
        unsigned current_channel_input_base = mul(no, mul(input_fm_h, input_fm_w));

        // Reset `oy_offset` for the current feature map.
        oy_offset = 0;

        // Iterate over the height of the pooling output.
        for (int oy = 0; oy < pool_out_h; oy++) {
            // Reset `ox_offset` for the current row of the pooling output.
            ox_offset = 0;

            // Iterate over the width of the pooling output.
            for (int ox = 0; ox < pool_out_w; ox++) {
                // Initialize `max` to the smallest possible short value for finding the maximum.
                short max = -32768; // SHRT_MIN

                // Iterate over the height of the pooling kernel window.
                for (int ky = 0; ky < kernel_size; ky++) {
                    // Calculate the y-coordinate in the input feature map for the current pooling window element.
                    int input_y = oy_offset + ky - pad;
                    // Calculate the offset for the row `input_y` within the input feature map.
                    input_y_offset = mul(input_y, input_fm_w);

                    // Iterate over the width of the pooling kernel window.
                    for (int kx = 0; kx < kernel_size; kx++) {
                        // Calculate the x-coordinate in the input feature map.
                        int input_x = ox_offset + kx - pad;

                        // Boundary check: Ensure the current input pixel is within valid bounds.
                        if (input_y >= 0 && input_y < input_fm_h && input_x >= 0 &&
                            input_x < input_fm_w) {
                            // Calculate the flattened 1D index for the current input pixel.
                            int input_index =
                                current_channel_input_base + input_y_offset + input_x;
                            // If the current input pixel value is greater than `max`, update `max`.
                            if (in[input_index] > max) {
                                max = in[input_index];
                            }
                        }
                        // Pixels outside the boundary are implicitly ignored in max pooling
                        // (or treated as -infinity, which wouldn't change the max unless all are outside).
                    } // End pooling kernel width loop (kx)
                } // End pooling kernel height loop (ky)

                // Write the maximum value found in the pooling window to the output.
                out[output_offset] = max;
                // Increment the global flattened output index.
                output_offset++;
                // Update `ox_offset` for the next pooling window in the row (strength reduction).
                ox_offset += stride;

            } // End pooling output width loop (ox)

            // Update `oy_offset` for the next row of pooling windows (strength reduction).
            oy_offset += stride;

        } // End pooling output height loop (oy)
    } // End feature map loop (no)
}


// =================================================================================================
//                                Hardware Accelerator Launch Function
// =================================================================================================
// Initiates a hardware accelerator (if `USE_HW_ACCEL` is defined) by writing to a GPIO
// start register and then polls a GPIO done register until the accelerator signals completion.
//
// This is a typical pattern for offloading computation to a dedicated hardware block.
// =================================================================================================
#ifdef USE_HW_ACCEL
void launch_hw_accel() {
    // --- GPIO Register Pointers ---
    // Volatile pointers to memory-mapped I/O (MMIO) registers for controlling the hardware accelerator.
    // `volatile` keyword prevents the compiler from optimizing away reads/writes to these addresses.
    volatile int *gpio_start = (void *)(GPIO_START_ADDR); // Start signal register
    volatile int *gpio_done  = (void *)(GPIO_DONE_ADDR);  // Done signal register

    // --- Start the Hardware Accelerator ---
    // Set a specific bit (e.g., bit 0) in the start register to trigger the accelerator.
    // The `|= 0x1` operation sets the least significant bit without affecting other bits.
    *gpio_start |= 0x1;

    // --- Wait for Completion ---
    // Continuously poll the done register until a specific bit (e.g., bit 0) is set by the hardware,
    // indicating that the accelerated task has finished.
    // This is a busy-wait loop.
    while (!(*gpio_done & 0x1)) {
        // Empty loop body; the condition check is the work.
        ; // Wait for the hardware accelerator to finish
    }
}
#endif // USE_HW_ACCEL

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
  printf("    Retired Instructions:      %u\n",
         (unsigned int)res.perf_retired_inst_count);
  printf("    Retired Loads:             %u\n",
         (unsigned int)res.perf_retired_load_count);
  printf("    Retired Stores:            %u\n",
         (unsigned int)res.perf_retired_store_count);
  printf("    Branches Executed:         %u\n",
         (unsigned int)res.perf_branch_executed_count);
  printf("    Branches Taken:            %u\n",
         (unsigned int)res.perf_branch_taken_count);
  printf("    IF Stalls:                 %u\n",
         (unsigned int)res.perf_if_stall_count);
  printf("    MEM Access Stalls:         %u\n",
         (unsigned int)res.perf_mem_access_stall_count);
  printf("    IW Stalls:                 %u\n",
         (unsigned int)res.perf_iw_stall_count);
  printf("    RDW Stalls:                %u\n",
         (unsigned int)res.perf_rdw_stall_count);
  printf("    Jumps Executed:            %u\n",
         (unsigned int)res.perf_jump_executed_count);
  printf("    ALU Ops Executed:          %u\n",
         (unsigned int)res.perf_alu_op_executed_count);
  printf("    Shift Ops Executed:        %u\n",
         (unsigned int)res.perf_shift_op_executed_count);
  printf("    NOPs in ID:                %u\n",
         (unsigned int)res.perf_nop_in_id_count);
  printf("    Total MEM Ops Issued:      %u\n",
         (unsigned int)res.perf_total_mem_ops_count);
  printf("    Register Writes:           %u\n",
         (unsigned int)res.perf_reg_writes_count);

  printf("benchmark finished\n");

  if (result == 0) {
    hit_good_trap();
  } else {
    nemu_assert(0);
  }

  return 0;
}
