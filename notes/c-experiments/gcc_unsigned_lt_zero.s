	.file	"unsigned_lt_zero.c"
	.text
	.p2align 4,,15
	.globl	f
	.type	f, @function
f:
.LFB0:
	.cfi_startproc
	xorl	%eax, %eax
	ret
	.cfi_endproc
.LFE0:
	.size	f, .-f
	.p2align 4,,15
	.globl	g
	.type	g, @function
g:
.LFB5:
	.cfi_startproc
	xorl	%eax, %eax
	ret
	.cfi_endproc
.LFE5:
	.size	g, .-g
	.p2align 4,,15
	.globl	h
	.type	h, @function
h:
.LFB7:
	.cfi_startproc
	xorl	%eax, %eax
	ret
	.cfi_endproc
.LFE7:
	.size	h, .-h
	.p2align 4,,15
	.globl	i
	.type	i, @function
i:
.LFB9:
	.cfi_startproc
	xorl	%eax, %eax
	ret
	.cfi_endproc
.LFE9:
	.size	i, .-i
	.ident	"GCC: (Ubuntu 7.5.0-3ubuntu1~18.04) 7.5.0"
	.section	.note.GNU-stack,"",@progbits
