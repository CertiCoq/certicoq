	.text
	.file	"unsigned_lt_zero.c"
	.globl	f                       # -- Begin function f
	.p2align	4, 0x90
	.type	f,@function
f:                                      # @f
	.cfi_startproc
# %bb.0:
	xorl	%eax, %eax
	retq
.Lfunc_end0:
	.size	f, .Lfunc_end0-f
	.cfi_endproc
                                        # -- End function
	.globl	g                       # -- Begin function g
	.p2align	4, 0x90
	.type	g,@function
g:                                      # @g
	.cfi_startproc
# %bb.0:
	xorl	%eax, %eax
	retq
.Lfunc_end1:
	.size	g, .Lfunc_end1-g
	.cfi_endproc
                                        # -- End function
	.globl	h                       # -- Begin function h
	.p2align	4, 0x90
	.type	h,@function
h:                                      # @h
	.cfi_startproc
# %bb.0:
	xorl	%eax, %eax
	retq
.Lfunc_end2:
	.size	h, .Lfunc_end2-h
	.cfi_endproc
                                        # -- End function
	.globl	i                       # -- Begin function i
	.p2align	4, 0x90
	.type	i,@function
i:                                      # @i
	.cfi_startproc
# %bb.0:
	xorl	%eax, %eax
	retq
.Lfunc_end3:
	.size	i, .Lfunc_end3-i
	.cfi_endproc
                                        # -- End function

	.ident	"clang version 6.0.0-1ubuntu2 (tags/RELEASE_600/final)"
	.section	".note.GNU-stack","",@progbits
