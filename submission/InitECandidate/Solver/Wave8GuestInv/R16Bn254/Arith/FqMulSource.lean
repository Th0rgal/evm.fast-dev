import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqInverseSource

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def montVar (name : String) : ExpHOL 64 := .var .local (ofString name)
def montLoExpr (e : ExpHOL 64) : ExpHOL 64 := .op .and [e, .const 4294967295]
def montHiExpr (e : ExpHOL 64) : ExpHOL 64 := .shift .lsr e (.const 32)

def montAccProduct (a b : ExpHOL 64) (tail : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local (ofString "pr") (.panop .mul [a,b]))
    (.seq (.assign .local (ofString "L") (.op .add [montVar "L", montLoExpr (montVar "pr")]))
      (.seq (.assign .local (ofString "H") (.op .add [montVar "H", montHiExpr (montVar "pr")])) tail))

def montAccProducts (products : List (ExpHOL 64 × ExpHOL 64)) (tail : ProgHOL 64) : ProgHOL 64 :=
  products.foldr (fun ab rest => montAccProduct ab.1 ab.2 rest) tail

def montLowerColumn (dest : String) (products : List (ExpHOL 64 × ExpHOL 64)) (tail : ProgHOL 64) : ProgHOL 64 :=
  montAccProducts products
    (.seq (.assign .local (ofString "col") (.op .add [montVar "L", montVar "c"]))
      (.seq (.assign .local (ofString "dg") (montLoExpr (montVar "col")))
        (.seq (.assign .local (ofString dest) (montLoExpr (.panop .mul [montVar "dg", .const 3834012553])))
          (.seq (.assign .local (ofString "pr") (.panop .mul [montVar dest, .const 3632069959]))
            (.seq (.assign .local (ofString "col2") (.op .add [montVar "dg", montLoExpr (montVar "pr")]))
              (.seq (.assign .local (ofString "c") (.op .add [montHiExpr (montVar "col"), montVar "H",
                montHiExpr (montVar "col2"), montHiExpr (montVar "pr")]))
                (.seq (.assign .local (ofString "L") (.const 0))
                  (.seq (.assign .local (ofString "H") (.const 0)) tail))))))))

def montUpperColumn (dest : String) (products : List (ExpHOL 64 × ExpHOL 64)) (tail : ProgHOL 64) : ProgHOL 64 :=
  montAccProducts products
    (.seq (.assign .local (ofString "col") (.op .add [montVar "L", montVar "c"]))
      (.seq (.assign .local (ofString dest) (montLoExpr (montVar "col")))
        (.seq (.assign .local (ofString "c") (.op .add [montHiExpr (montVar "col"), montVar "H"]))
          (.seq (.assign .local (ofString "L") (.const 0))
            (.seq (.assign .local (ofString "H") (.const 0)) tail)))))

def fqMulFinish : ProgHOL 64 :=
  .dec (ofString "r") arithU256Shape
    (.rstruct [
      .op .or [montVar "u0", .shift .lsl (montVar "u1") (.const 32)],
      .op .or [montVar "u2", .shift .lsl (montVar "u3") (.const 32)],
      .op .or [montVar "u4", .shift .lsl (montVar "u5") (.const 32)],
      .op .or [montVar "u6", .shift .lsl (montVar "c") (.const 32)]])
    (.decCall (ofString "lt") .one (ofString "u256_lt") [montVar "r", limbs256ConstExpr fqModulus]
      (.seq (.ite (.cmp .equal (montVar "lt") (.const 0))
        (.call none (ofString "u256_sub") [montVar "r", limbs256ConstExpr fqModulus]) .skip)
        (.return (montVar "r"))))

def fqMulColumn14 : ProgHOL 64 :=
  montUpperColumn "u6"
    [(montVar "a7", montVar "b7"),
     (montVar "m7", .const 811880050)] fqMulFinish

def fqMulColumn13 : ProgHOL 64 :=
  montUpperColumn "u5"
    [(montVar "a6", montVar "b7"),
     (montVar "a7", montVar "b6"),
     (montVar "m6", .const 811880050),
     (montVar "m7", .const 3778125865)] fqMulColumn14

def fqMulColumn12 : ProgHOL 64 :=
  montUpperColumn "u4"
    [(montVar "a5", montVar "b7"),
     (montVar "a6", montVar "b6"),
     (montVar "a7", montVar "b5"),
     (montVar "m5", .const 811880050),
     (montVar "m6", .const 3778125865),
     (montVar "m7", .const 3092268470)] fqMulColumn13

def fqMulColumn11 : ProgHOL 64 :=
  montUpperColumn "u3"
    [(montVar "a4", montVar "b7"),
     (montVar "a5", montVar "b6"),
     (montVar "a6", montVar "b5"),
     (montVar "a7", montVar "b4"),
     (montVar "m4", .const 811880050),
     (montVar "m5", .const 3778125865),
     (montVar "m6", .const 3092268470),
     (montVar "m7", .const 2172737629)] fqMulColumn12

def fqMulColumn10 : ProgHOL 64 :=
  montUpperColumn "u2"
    [(montVar "a3", montVar "b7"),
     (montVar "a4", montVar "b6"),
     (montVar "a5", montVar "b5"),
     (montVar "a6", montVar "b4"),
     (montVar "a7", montVar "b3"),
     (montVar "m3", .const 811880050),
     (montVar "m4", .const 3778125865),
     (montVar "m5", .const 3092268470),
     (montVar "m6", .const 2172737629),
     (montVar "m7", .const 2541841041)] fqMulColumn11

def fqMulColumn9 : ProgHOL 64 :=
  montUpperColumn "u1"
    [(montVar "a2", montVar "b7"),
     (montVar "a3", montVar "b6"),
     (montVar "a4", montVar "b5"),
     (montVar "a5", montVar "b4"),
     (montVar "a6", montVar "b3"),
     (montVar "a7", montVar "b2"),
     (montVar "m2", .const 811880050),
     (montVar "m3", .const 3778125865),
     (montVar "m4", .const 3092268470),
     (montVar "m5", .const 2172737629),
     (montVar "m6", .const 2541841041),
     (montVar "m7", .const 1752287885)] fqMulColumn10

def fqMulColumn8 : ProgHOL 64 :=
  montUpperColumn "u0"
    [(montVar "a1", montVar "b7"),
     (montVar "a2", montVar "b6"),
     (montVar "a3", montVar "b5"),
     (montVar "a4", montVar "b4"),
     (montVar "a5", montVar "b3"),
     (montVar "a6", montVar "b2"),
     (montVar "a7", montVar "b1"),
     (montVar "m1", .const 811880050),
     (montVar "m2", .const 3778125865),
     (montVar "m3", .const 3092268470),
     (montVar "m4", .const 2172737629),
     (montVar "m5", .const 2541841041),
     (montVar "m6", .const 1752287885),
     (montVar "m7", .const 1008765974)] fqMulColumn9

def fqMulColumn7 : ProgHOL 64 :=
  montLowerColumn "m7"
    [(montVar "a0", montVar "b7"),
     (montVar "a1", montVar "b6"),
     (montVar "a2", montVar "b5"),
     (montVar "a3", montVar "b4"),
     (montVar "a4", montVar "b3"),
     (montVar "a5", montVar "b2"),
     (montVar "a6", montVar "b1"),
     (montVar "a7", montVar "b0"),
     (montVar "m0", .const 811880050),
     (montVar "m1", .const 3778125865),
     (montVar "m2", .const 3092268470),
     (montVar "m3", .const 2172737629),
     (montVar "m4", .const 2541841041),
     (montVar "m5", .const 1752287885),
     (montVar "m6", .const 1008765974)] fqMulColumn8

def fqMulColumn6 : ProgHOL 64 :=
  montLowerColumn "m6"
    [(montVar "a0", montVar "b6"),
     (montVar "a1", montVar "b5"),
     (montVar "a2", montVar "b4"),
     (montVar "a3", montVar "b3"),
     (montVar "a4", montVar "b2"),
     (montVar "a5", montVar "b1"),
     (montVar "a6", montVar "b0"),
     (montVar "m0", .const 3778125865),
     (montVar "m1", .const 3092268470),
     (montVar "m2", .const 2172737629),
     (montVar "m3", .const 2541841041),
     (montVar "m4", .const 1752287885),
     (montVar "m5", .const 1008765974)] fqMulColumn7

def fqMulColumn5 : ProgHOL 64 :=
  montLowerColumn "m5"
    [(montVar "a0", montVar "b5"),
     (montVar "a1", montVar "b4"),
     (montVar "a2", montVar "b3"),
     (montVar "a3", montVar "b2"),
     (montVar "a4", montVar "b1"),
     (montVar "a5", montVar "b0"),
     (montVar "m0", .const 3092268470),
     (montVar "m1", .const 2172737629),
     (montVar "m2", .const 2541841041),
     (montVar "m3", .const 1752287885),
     (montVar "m4", .const 1008765974)] fqMulColumn6

def fqMulColumn4 : ProgHOL 64 :=
  montLowerColumn "m4"
    [(montVar "a0", montVar "b4"),
     (montVar "a1", montVar "b3"),
     (montVar "a2", montVar "b2"),
     (montVar "a3", montVar "b1"),
     (montVar "a4", montVar "b0"),
     (montVar "m0", .const 2172737629),
     (montVar "m1", .const 2541841041),
     (montVar "m2", .const 1752287885),
     (montVar "m3", .const 1008765974)] fqMulColumn5

def fqMulColumn3 : ProgHOL 64 :=
  montLowerColumn "m3"
    [(montVar "a0", montVar "b3"),
     (montVar "a1", montVar "b2"),
     (montVar "a2", montVar "b1"),
     (montVar "a3", montVar "b0"),
     (montVar "m0", .const 2541841041),
     (montVar "m1", .const 1752287885),
     (montVar "m2", .const 1008765974)] fqMulColumn4

def fqMulColumn2 : ProgHOL 64 :=
  montLowerColumn "m2"
    [(montVar "a0", montVar "b2"),
     (montVar "a1", montVar "b1"),
     (montVar "a2", montVar "b0"),
     (montVar "m0", .const 1752287885),
     (montVar "m1", .const 1008765974)] fqMulColumn3

def fqMulColumn1 : ProgHOL 64 :=
  montLowerColumn "m1"
    [(montVar "a0", montVar "b1"),
     (montVar "a1", montVar "b0"),
     (montVar "m0", .const 1008765974)] fqMulColumn2

def fqMulColumn0 : ProgHOL 64 :=
  montLowerColumn "m0"
    [(montVar "a0", montVar "b0")] fqMulColumn1

def fqMulInitializers : List (String × ExpHOL 64) :=
  [("a0", montLoExpr (.rfield 0 (montVar "a"))),
   ("a1", montHiExpr (.rfield 0 (montVar "a"))),
   ("a2", montLoExpr (.rfield 1 (montVar "a"))),
   ("a3", montHiExpr (.rfield 1 (montVar "a"))),
   ("a4", montLoExpr (.rfield 2 (montVar "a"))),
   ("a5", montHiExpr (.rfield 2 (montVar "a"))),
   ("a6", montLoExpr (.rfield 3 (montVar "a"))),
   ("a7", montHiExpr (.rfield 3 (montVar "a"))),
   ("b0", montLoExpr (.rfield 0 (montVar "b"))),
   ("b1", montHiExpr (.rfield 0 (montVar "b"))),
   ("b2", montLoExpr (.rfield 1 (montVar "b"))),
   ("b3", montHiExpr (.rfield 1 (montVar "b"))),
   ("b4", montLoExpr (.rfield 2 (montVar "b"))),
   ("b5", montHiExpr (.rfield 2 (montVar "b"))),
   ("b6", montLoExpr (.rfield 3 (montVar "b"))),
   ("b7", montHiExpr (.rfield 3 (montVar "b"))),
   ("pr", .const 0),
   ("L", .const 0),
   ("H", .const 0),
   ("c", .const 0),
   ("col", .const 0),
   ("col2", .const 0),
   ("dg", .const 0),
   ("m0", .const 0),
   ("m1", .const 0),
   ("m2", .const 0),
   ("m3", .const 0),
   ("m4", .const 0),
   ("m5", .const 0),
   ("m6", .const 0),
   ("m7", .const 0),
   ("u0", .const 0),
   ("u1", .const 0),
   ("u2", .const 0),
   ("u3", .const 0),
   ("u4", .const 0),
   ("u5", .const 0),
   ("u6", .const 0)]

def fqMulProgram : ProgHOL 64 :=
  fqMulInitializers.foldr (fun ne tail => .dec (ofString ne.1) .one ne.2 tail) fqMulColumn0

theorem fqMul_source_eq : arithSourceBody Guest.Software.guestFn_fq_mul = fqMulProgram := rfl

end InitECandidate.Solver.Wave8GuestInv.Arith
