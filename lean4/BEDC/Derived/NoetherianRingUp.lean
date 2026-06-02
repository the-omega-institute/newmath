import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NoetherianRingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive NoetherianRingUp : Type where
  | mk (C I A G H Q P N : BHist) :
      UnaryHistory N → hsame N C → NoetherianRingUp

def noetherianRingFields : NoetherianRingUp → List BHist
  | NoetherianRingUp.mk C I A G H Q P N _ _ => [C, I, A, G, H, Q, P, N]

theorem NoetherianRingCarrier_namecert_obligations [AskSetup] [PackageSetup]
    (R : NoetherianRingUp)
    {C I A G H Q P N chainRead generatorRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    noetherianRingFields R = [C, I, A, G, H, Q, P, N] →
      UnaryHistory C →
        UnaryHistory I →
          UnaryHistory A →
            UnaryHistory G →
              UnaryHistory H →
                UnaryHistory Q →
                  Cont C I chainRead →
                    Cont A G generatorRead →
                      Cont H Q replayRead →
                        PkgSig bundle P pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row N ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row C ∨ hsame row I ∨ hsame row A ∨
                                  hsame row G ∨ Cont C I chainRead ∨
                                    Cont A G generatorRead ∨ Cont H Q replayRead)
                              (fun row : BHist => PkgSig bundle P pkg ∧ hsame row N)
                              hsame ∧
                            UnaryHistory chainRead ∧ UnaryHistory generatorRead ∧
                              UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro fieldsEq unaryC unaryI unaryA unaryG unaryH unaryQ chainCont generatorCont
    replayCont pkgP
  rcases R with ⟨c0, i0, a0, g0, h0, q0, p0, n0, unaryn0, nameToSource0⟩
  cases fieldsEq
  have chainUnary : UnaryHistory chainRead :=
    unary_cont_closed unaryC unaryI chainCont
  have generatorUnary : UnaryHistory generatorRead :=
    unary_cont_closed unaryA unaryG generatorCont
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed unaryH unaryQ replayCont
  have sourceN :
          (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, unaryn0⟩
  have cert :
          SemanticNameCert
              (fun row : BHist => hsame row N ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row C ∨ hsame row I ∨ hsame row A ∨ hsame row G ∨
                  Cont C I chainRead ∨ Cont A G generatorRead ∨
                    Cont H Q replayRead)
              (fun row : BHist => PkgSig bundle P pkg ∧ hsame row N)
              hsame := by
    exact {
      core := {
            carrier_inhabited := Exists.intro N sourceN
            equiv_refl := by
              intro row _source
              exact hsame_refl row
            equiv_symm := by
              intro _row _other sameRows
              exact hsame_symm sameRows
            equiv_trans := by
              intro _row _middle _other sameLeft sameRight
              exact hsame_trans sameLeft sameRight
            carrier_respects_equiv := by
              intro _row _other sameRows source
              exact
                ⟨hsame_trans (hsame_symm sameRows) source.left,
                  unary_transport source.right sameRows⟩
          }
      pattern_sound := by
            intro _row source
            exact Or.inl (hsame_trans source.left nameToSource0)
      ledger_sound := by
            intro _row source
            exact ⟨pkgP, source.left⟩
    }
  exact ⟨cert, chainUnary, generatorUnary, replayUnary⟩

end BEDC.Derived.NoetherianRingUp
