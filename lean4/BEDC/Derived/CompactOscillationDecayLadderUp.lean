import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompactOscillationDecayLadderUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CompactOscillationDecayLadderCarrier [AskSetup] [PackageSetup]
    (K O D F R E U H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory K ∧ UnaryHistory O ∧ UnaryHistory D ∧ UnaryHistory F ∧ UnaryHistory R ∧
    UnaryHistory E ∧ UnaryHistory U ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont H C (append H C) ∧ PkgSig bundle P pkg

theorem CompactOscillationDecayLadderCarrier_uniform_modulus_handoff [AskSetup]
    [PackageSetup]
    {K O D F R E U H C P N oscillationRead modulusRead decayRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactOscillationDecayLadderCarrier K O D F R E U H C P N bundle pkg ->
      Cont O D oscillationRead ->
        Cont oscillationRead F modulusRead ->
          Cont modulusRead U decayRead ->
            Cont decayRead N sealRead ->
              PkgSig bundle P pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row K ∨ hsame row O ∨ hsame row D ∨ hsame row F ∨
                        hsame row R ∨ hsame row E ∨ hsame row U ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont O D oscillationRead ∧
                        Cont oscillationRead F modulusRead ∧
                          Cont modulusRead U decayRead ∧ Cont decayRead N sealRead ∧
                            PkgSig bundle P pkg)
                    hsame ∧ UnaryHistory oscillationRead ∧ UnaryHistory modulusRead ∧
                      UnaryHistory decayRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: CompactOscillationDecayLadderCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier oscillationRoute modulusRoute decayRoute sealRoute pPkg
  obtain ⟨_unaryK, unaryO, unaryD, unaryF, _unaryR, _unaryE, unaryU, _unaryH, _unaryC,
    _unaryP, unaryN, _transportRoute, _carrierPkg⟩ := carrier
  have oscillationUnary : UnaryHistory oscillationRead :=
    unary_cont_closed unaryO unaryD oscillationRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed oscillationUnary unaryF modulusRoute
  have decayUnary : UnaryHistory decayRead :=
    unary_cont_closed modulusUnary unaryU decayRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed decayUnary unaryN sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row O ∨ hsame row D ∨ hsame row F ∨ hsame row R ∨
              hsame row E ∨ hsame row U ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont O D oscillationRead ∧
              Cont oscillationRead F modulusRead ∧ Cont modulusRead U decayRead ∧
                Cont decayRead N sealRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, oscillationRoute, modulusRoute, decayRoute, sealRoute, pPkg⟩
  }
  exact ⟨cert, oscillationUnary, modulusUnary, decayUnary, sealUnary⟩

end BEDC.Derived.CompactOscillationDecayLadderUp
