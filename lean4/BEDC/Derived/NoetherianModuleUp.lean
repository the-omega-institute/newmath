import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NoetherianModuleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

inductive NoetherianModuleUp : Type where
  | mk (M R I A G H Q P N : BHist) :
      UnaryHistory N → hsame N M → NoetherianModuleUp

def noetherianModuleFields : NoetherianModuleUp → List BHist
  | NoetherianModuleUp.mk M R I A G H Q P N _ _ => [M, R, I, A, G, H, Q, P, N]

theorem NoetherianModuleCarrier_namecert_obligations [AskSetup] [PackageSetup]
    (M0 : NoetherianModuleUp)
    {M R I A G H Q P N scalarRead idealRead stabilizationRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    noetherianModuleFields M0 = [M, R, I, A, G, H, Q, P, N] →
      UnaryHistory M →
        UnaryHistory R →
          UnaryHistory I →
            UnaryHistory A →
              UnaryHistory G →
                UnaryHistory H →
                  UnaryHistory Q →
                    Cont M R scalarRead →
                      Cont R I idealRead →
                        Cont A G stabilizationRead →
                          Cont H Q replayRead →
                            PkgSig bundle P pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row M ∨ hsame row R ∨ hsame row I ∨
                                      hsame row A ∨ hsame row G ∨ Cont M R scalarRead ∨
                                        Cont R I idealRead ∨ Cont A G stabilizationRead ∨
                                          Cont H Q replayRead)
                                  (fun row : BHist => PkgSig bundle P pkg ∧ hsame row N)
                                  hsame ∧
                                UnaryHistory scalarRead ∧ UnaryHistory idealRead ∧
                                  UnaryHistory stabilizationRead ∧
                                    UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro fieldsEq unaryM unaryR unaryI unaryA unaryG unaryH unaryQ scalarCont idealCont
    stabilizationCont replayCont pkgP
  rcases M0 with ⟨m0, r0, i0, a0, g0, h0, q0, p0, n0, unaryn0, nameToSource0⟩
  cases fieldsEq
  have scalarUnary : UnaryHistory scalarRead :=
    unary_cont_closed unaryM unaryR scalarCont
  have idealUnary : UnaryHistory idealRead :=
    unary_cont_closed unaryR unaryI idealCont
  have stabilizationUnary : UnaryHistory stabilizationRead :=
    unary_cont_closed unaryA unaryG stabilizationCont
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed unaryH unaryQ replayCont
  have sourceN :
          (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, unaryn0⟩
  have cert :
          SemanticNameCert
              (fun row : BHist => hsame row N ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row R ∨ hsame row I ∨ hsame row A ∨
                  hsame row G ∨ Cont M R scalarRead ∨ Cont R I idealRead ∨
                    Cont A G stabilizationRead ∨ Cont H Q replayRead)
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
  exact ⟨cert, scalarUnary, idealUnary, stabilizationUnary, replayUnary⟩

end BEDC.Derived.NoetherianModuleUp
