	.file	"tailcall.c"
	.text
	.p2align 4
	.globl	g4
	.type	g4, @function
g4:
.LFB0:
	.cfi_startproc
	endbr64
	movq	%rdi, %r8
	movq	%rsi, %rdi
	leaq	(%rsi,%r8), %rsi
	jmp	f4@PLT
	.cfi_endproc
.LFE0:
	.size	g4, .-g4
	.p2align 4
	.globl	g3
	.type	g3, @function
g3:
.LFB1:
	.cfi_startproc
	endbr64
	movq	%rdi, %r8
	xorl	%ecx, %ecx
	movq	%rsi, %rdi
	leaq	(%rsi,%r8), %rsi
	jmp	f4@PLT
	.cfi_endproc
.LFE1:
	.size	g3, .-g3
	.p2align 4
	.globl	g6
	.type	g6, @function
g6:
.LFB2:
	.cfi_startproc
	endbr64
	movq	%rdi, %r8
	movq	%rsi, %rdi
	leaq	(%rsi,%r8), %rsi
	jmp	f4@PLT
	.cfi_endproc
.LFE2:
	.size	g6, .-g6
	.p2align 4
	.globl	h3
	.type	h3, @function
h3:
.LFB3:
	.cfi_startproc
	endbr64
	subq	$8, %rsp
	.cfi_def_cfa_offset 16
	movq	%rdx, %r9
	movq	%rsi, %r8
	movq	%rdi, %rcx
	pushq	%rdi
	.cfi_def_cfa_offset 24
	pushq	%rdx
	.cfi_def_cfa_offset 32
	pushq	%rsi
	.cfi_def_cfa_offset 40
	pushq	%rdi
	.cfi_def_cfa_offset 48
	pushq	%rdx
	.cfi_def_cfa_offset 56
	pushq	%rsi
	.cfi_def_cfa_offset 64
	pushq	%rdi
	.cfi_def_cfa_offset 72
	pushq	%rdx
	.cfi_def_cfa_offset 80
	pushq	%rsi
	.cfi_def_cfa_offset 88
	pushq	%rdi
	.cfi_def_cfa_offset 96
	call	f16@PLT
	addq	$88, %rsp
	.cfi_def_cfa_offset 8
	ret
	.cfi_endproc
.LFE3:
	.size	h3, .-h3
	.p2align 4
	.globl	h16
	.type	h16, @function
h16:
.LFB4:
	.cfi_startproc
	endbr64
	movq	%rdx, %r11
	movq	%rcx, %rdx
	movq	72(%rsp), %rcx
	movq	80(%rsp), %rax
	movq	%rdi, %r10
	movq	%rsi, %rdi
	movq	%rcx, 80(%rsp)
	movq	%r10, %rsi
	movq	%r11, %rcx
	movq	%rax, 72(%rsp)
	jmp	f16@PLT
	.cfi_endproc
.LFE4:
	.size	h16, .-h16
	.p2align 4
	.globl	j16
	.type	j16, @function
j16:
.LFB5:
	.cfi_startproc
	endbr64
	movq	%rsi, %r11
	movq	8(%rsp), %rsi
	addq	%rcx, %rdx
	movq	48(%rsp), %r10
	addq	%r11, %rdx
	addq	40(%rsp), %r10
	movq	56(%rsp), %rcx
	addq	32(%rsp), %r10
	addq	%r9, %rsi
	addq	24(%rsp), %r10
	addq	%rdx, %rdi
	addq	16(%rsp), %rsi
	movq	%r10, %rdx
	addq	%r8, %rsi
	jmp	f4@PLT
	.cfi_endproc
.LFE5:
	.size	j16, .-j16
	.ident	"GCC: (Ubuntu 9.3.0-10ubuntu2) 9.3.0"
	.section	.note.GNU-stack,"",@progbits
	.section	.note.gnu.property,"a"
	.align 8
	.long	 1f - 0f
	.long	 4f - 1f
	.long	 5
0:
	.string	 "GNU"
1:
	.align 8
	.long	 0xc0000002
	.long	 3f - 2f
2:
	.long	 0x3
3:
	.align 8
4:
