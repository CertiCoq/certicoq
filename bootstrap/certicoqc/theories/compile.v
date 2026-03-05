From CertiCoq.Plugin Require Import CertiCoq.
From MetaRocq.Utils Require Import utils.
Open Scope bs_scope.

Require Import CertiCoq.Compiler.pipeline.
From CertiCoq.Plugin Require Import CertiCoq.
From CertiCoq.CertiCoqC Require Import CertiCoqC.

Set Warnings "-primitive-turned-into-axiom".

CertiCoq Compile -time -O 1 certicoqc.
CertiCoq Generate Glue -file "glue" [ ].
