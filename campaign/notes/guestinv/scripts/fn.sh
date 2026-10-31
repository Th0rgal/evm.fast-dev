#!/bin/sh
# usage: fn.sh NAME  -> prints guestFn_NAME body with line numbers
awk -v n="def guestFn_$1 :" 'index($0,n)==1{p=1} p&&/^def /&&index($0,n)!=1{exit} p{print NR": "$0}' ${AST:-$(dirname "$0")/../../../../Guest/SoftwareAst.lean} | sed -E 's/\(BitVec\.ofNat 64 ([0-9]+)\)/\1/g; s/Exp\.var VarKind\.local /L:/g; s/Exp\.var VarKind\.global /G:/g; s/Exp\.const /#/g; s/Exp\.//g; s/Prog\.//g; s/BinOp\.//g; s/Cmp\.//g; s/OpSize\.//g'
