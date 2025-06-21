.data
last_tail_ptr:
        .word 0

.globl intr_handler
	.align  2
	.type intr_handler, @function
	.section .exception

intr_handler:
	# TODO: Please add your own interrupt handler for DMA engine 
  lui $k0, 0x6002 # load DMA base adress into k0

  # clear sign bit (bit 31)
  lw $k0, 0x14($k0)        # load ctrl_stat register
  lui $k1, 0x7FFF          # load upper part of mask to clear sign bit
  ori $k1, $k1, 0xFFFF     # load lower part of mask to clear sign bit
  and $k1, $k0, $k1        # clear sign bit in ctrl_stat register
  lui $k0, 0x6002          # reload DMA base address into k1
  sw $k1, 0x14($k0)        # store back to ctrl_stat register

  # calculate tail_ptr_new and its increment
  lw $k1, 0x08($k0)        # load tail_ptr into $k1
  lw $k0, last_tail_ptr    # load last_tail_ptr into $k0
  sub $k0, $k1, $k0        # $k0 = delta = tail_ptr - last_tail_ptr
  sw $k1, last_tail_ptr    # update last_tail_ptr
  blez $k0, L2             # if delta <= 0, skip further processing
  NOP

L1:
  # calculate number of buffers to be processed
  # now $k0 contains delta, which is the number of bytes that has been processed
  lw $k1, 0x10($0)         # load dma_buf_stat into $k1
  addi $k1, $k1, -1        # decrement buffer status, at least one buffer is processed
  sw $k1, 0x10($0)         # store back to dma_buf_stat
  lui $k1, 0x6002          # reload DMA base address into $k1
  lw $k1, 0x10($k1)        # load dma_size into $k1
  sub $k0, $k0, $k1        # $k0 = delta - dma_size
  bgtz $k0, L1             # if delta > dma_size, process more buffers
  NOP

L2:
  # ereturn from interrupt
  eret
