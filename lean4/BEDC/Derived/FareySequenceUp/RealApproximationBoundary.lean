import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceRealApproximationBoundary [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N dyadicRead streamRead regularRead
      approxRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont Q T dyadicRead ->
        Cont dyadicRead W streamRead ->
          Cont streamRead R regularRead ->
            Cont regularRead G approxRead ->
              Cont approxRead E realSeal ->
                PkgSig bundle P pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row approxRead ∨ hsame row realSeal)
                    (fun row : BHist =>
                      hsame row Q ∨ hsame row T ∨ hsame row W ∨ hsame row R ∨
                        hsame row G ∨ hsame row E ∨ hsame row approxRead ∨
                          hsame row realSeal)
                    (fun row : BHist =>
                      PkgSig bundle P pkg ∧ (hsame row approxRead ∨ hsame row realSeal))
                    hsame ∧
                    UnaryHistory dyadicRead ∧ UnaryHistory streamRead ∧
                      UnaryHistory regularRead ∧ UnaryHistory approxRead ∧
                        UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier routeDyadic routeStream routeRegular routeApprox routeSeal pkgP
  rcases carrier with
    ⟨_unaryB, _unaryA, _unaryM, _unaryL, unaryT, _unaryS, _unaryD, unaryQ,
      unaryW, unaryR, unaryG, unaryE, _unaryH, _unaryC, _unaryP, _unaryN,
      _emptyA, _emptyS, _emptyM, _emptyG, _emptyE, _pkgCarrier⟩
  have unaryDyadic : UnaryHistory dyadicRead :=
    unary_cont_closed unaryQ unaryT routeDyadic
  have unaryStream : UnaryHistory streamRead :=
    unary_cont_closed unaryDyadic unaryW routeStream
  have unaryRegular : UnaryHistory regularRead :=
    unary_cont_closed unaryStream unaryR routeRegular
  have unaryApprox : UnaryHistory approxRead :=
    unary_cont_closed unaryRegular unaryG routeApprox
  have unarySeal : UnaryHistory realSeal :=
    unary_cont_closed unaryApprox unaryE routeSeal
  have sourceApprox :
      (fun row : BHist => hsame row approxRead ∨ hsame row realSeal) approxRead := by
    exact Or.inl (hsame_refl approxRead)
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row approxRead ∨ hsame row realSeal)
        (fun row : BHist =>
          hsame row Q ∨ hsame row T ∨ hsame row W ∨ hsame row R ∨ hsame row G ∨
            hsame row E ∨ hsame row approxRead ∨ hsame row realSeal)
        (fun row : BHist =>
          PkgSig bundle P pkg ∧ (hsame row approxRead ∨ hsame row realSeal))
        hsame := {
    core := {
      carrier_inhabited := Exists.intro approxRead sourceApprox
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
        intro row other sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro row source
      cases source with
      | inl sameApprox =>
          right
          right
          right
          right
          right
          right
          left
          exact sameApprox
      | inr sameSeal =>
          right
          right
          right
          right
          right
          right
          right
          exact sameSeal
    ledger_sound := by
      intro row source
      exact ⟨pkgP, source⟩
  }
  exact ⟨cert, unaryDyadic, unaryStream, unaryRegular, unaryApprox, unarySeal⟩

end BEDC.Derived.FareySequenceUp
