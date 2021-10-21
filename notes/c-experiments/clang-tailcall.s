	.file	"tailcall.c"
	.text
	.globl	g4
	.align	16, 0x90
	.type	g4,@function
g4:                                     # @g4
	.cfi_startproc
# BB#0:
	movq	%rdi, %rax
	addq	%rsi, %rax
	movq	%rsi, %rdi
	movq	%rax, %rsi
	jmp	f4                      # TAILCALL
.Ltmp0:
	.size	g4, .Ltmp0-g4
	.cfi_endproc

	.globl	g3
	.align	16, 0x90
	.type	g3,@function
g3:                                     # @g3
	.cfi_startproc
# BB#0:
	movq	%rdi, %rax
	addq	%rsi, %rax
	xorl	%ecx, %ecx
	movq	%rsi, %rdi
	movq	%rax, %rsi
	jmp	f4                      # TAILCALL
.Ltmp1:
	.size	g3, .Ltmp1-g3
	.cfi_endproc

	.globl	g6
	.align	16, 0x90
	.type	g6,@function
g6:                                     # @g6
	.cfi_startproc
# BB#0:
	movq	%rdi, %rax
	addq	%rsi, %rax
	movq	%rsi, %rdi
	movq	%rax, %rsi
	jmp	f4                      # TAILCALL
.Ltmp2:
	.size	g6, .Ltmp2-g6
	.cfi_endproc

	.globl	h3
	.align	16, 0x90
	.type	h3,@function
h3:                                     # @h3
	.cfi_startproc
# BB#0:
	subq	$88, %rsp
.Ltmp4:
	.cfi_def_cfa_offset 96
	movq	%rdi, 72(%rsp)
	movq	%rdx, 64(%rsp)
	movq	%rsi, 56(%rsp)
	movq	%rdi, 48(%rsp)
	movq	%rdx, 40(%rsp)
	movq	%rsi, 32(%rsp)
	movq	%rdi, 24(%rsp)
	movq	%rdx, 16(%rsp)
	movq	%rsi, 8(%rsp)
	movq	%rdi, (%rsp)
	movq	%rdi, %rcx
	movq	%rsi, %r8
	movq	%rdx, %r9
	callq	f16
	addq	$88, %rsp
	ret
.Ltmp5:
	.size	h3, .Ltmp5-h3
	.cfi_endproc

	.globl	h16
	.align	16, 0x90
	.type	h16,@function
h16:                                    # @h16
	.cfi_startproc
# BB#0:
	pushq	%rbp
.Ltmp13:
	.cfi_def_cfa_offset 16
	pushq	%r15
.Ltmp14:
	.cfi_def_cfa_offset 24
	pushq	%r14
.Ltmp15:
	.cfi_def_cfa_offset 32
	pushq	%r13
.Ltmp16:
	.cfi_def_cfa_offset 40
	pushq	%r12
.Ltmp17:
	.cfi_def_cfa_offset 48
	pushq	%rbx
.Ltmp18:
	.cfi_def_cfa_offset 56
	subq	$88, %rsp
.Ltmp19:
	.cfi_def_cfa_offset 144
.Ltmp20:
	.cfi_offset %rbx, -56
.Ltmp21:
	.cfi_offset %r12, -48
.Ltmp22:
	.cfi_offset %r13, -40
.Ltmp23:
	.cfi_offset %r14, -32
.Ltmp24:
	.cfi_offset %r15, -24
.Ltmp25:
	.cfi_offset %rbp, -16
	movq	%rdx, %rax
	movq	%rdi, %rdx
	movq	152(%rsp), %r11
	movq	160(%rsp), %r14
	movq	168(%rsp), %r15
	movq	176(%rsp), %r12
	movq	184(%rsp), %r13
	movq	192(%rsp), %r10
	movq	200(%rsp), %rbx
	movq	216(%rsp), %rbp
	movq	208(%rsp), %rdi
	movq	%rdi, 72(%rsp)
	movq	%rbp, 64(%rsp)
	movq	%rbx, 56(%rsp)
	movq	%r10, 48(%rsp)
	movq	%r13, 40(%rsp)
	movq	%r12, 32(%rsp)
	movq	%r15, 24(%rsp)
	movq	%r14, 16(%rsp)
	movq	%r11, 8(%rsp)
	movq	144(%rsp), %rdi
	movq	%rdi, (%rsp)
	movq	%rsi, %rdi
	movq	%rdx, %rsi
	movq	%rcx, %rdx
	movq	%rax, %rcx
	callq	f16
	addq	$88, %rsp
	popq	%rbx
	popq	%r12
	popq	%r13
	popq	%r14
	popq	%r15
	popq	%rbp
	ret
.Ltmp26:
	.size	h16, .Ltmp26-h16
	.cfi_endproc

	.globl	j16
	.align	16, 0x90
	.type	j16,@function
j16:                                    # @j16
	.cfi_startproc
# BB#0:
	movq	56(%rsp), %r10
	movq	32(%rsp), %rax
	addq	%rsi, %rdi
	addq	%rdx, %rdi
	addq	%rcx, %rdi
	addq	%r9, %r8
	addq	8(%rsp), %r8
	addq	16(%rsp), %r8
	addq	24(%rsp), %rax
	addq	40(%rsp), %rax
	addq	48(%rsp), %rax
	movq	%r8, %rsi
	movq	%rax, %rdx
	movq	%r10, %rcx
	jmp	f4                      # TAILCALL
.Ltmp27:
	.size	j16, .Ltmp27-j16
	.cfi_endproc

	.globl	h8
	.align	16, 0x90
	.type	h8,@function
h8:                                     # @h8
	.cfi_startproc
# BB#0:
	movq	%rdx, %rax
	movq	%rdi, %rdx
	movq	%rsi, %rdi
	movq	%rdx, %rsi
	movq	%rcx, %rdx
	movq	%rax, %rcx
	jmp	f8                      # TAILCALL
.Ltmp28:
	.size	h8, .Ltmp28-h8
	.cfi_endproc

	.globl	h12
	.align	16, 0x90
	.type	h12,@function
h12:                                    # @h12
	.cfi_startproc
# BB#0:
	movq	%rdx, %rax
	movq	%rdi, %rdx
	movq	%rsi, %rdi
	movq	%rdx, %rsi
	movq	%rcx, %rdx
	movq	%rax, %rcx
	jmp	f12                     # TAILCALL
.Ltmp29:
	.size	h12, .Ltmp29-h12
	.cfi_endproc


	.ident	"clang version 3.4.2 (tags/RELEASE_34/dot2-final)"
	.section	".note.GNU-stack","",@progbits
