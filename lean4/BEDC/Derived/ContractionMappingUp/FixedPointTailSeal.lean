import BEDC.Derived.ContractionMappingUp.ScopedDependencySurface
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ContractionMappingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContractionMappingCarrier_fixed_point_tail_seal [AskSetup] [PackageSetup]
    {X d T G lambda M I H C P N x0 iterates boundPower tolerance adjacentReplay tailReplay
      tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContractionMappingCarrier X d T G lambda M I H C P N bundle pkg →
      ContractionMappingOrbitLedger x0 iterates boundPower tolerance adjacentReplay
        tailReplay →
        Cont I M tailRead →
          Cont tailRead C sealRead →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row I ∨ hsame row M ∨ hsame row tailRead ∨
                      hsame row sealRead ∨ Cont I M tailRead ∨ Cont tailRead C sealRead)
                  (fun row : BHist =>
                    PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg ∧
                      hsame row sealRead)
                  hsame ∧
                UnaryHistory tailRead ∧ UnaryHistory sealRead ∧ Cont I M tailRead ∧
                  Cont tailRead C sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier _orbit tailRoute sealRoute sealPkg
  obtain ⟨_XUnary, _dUnary, _TUnary, _GUnary, _lambdaUnary, MUnary, IUnary, _HUnary,
    CUnary, _PUnary, _NUnary, provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed IUnary MUnary tailRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary CUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row M ∨ hsame row tailRead ∨ hsame row sealRead ∨
              Cont I M tailRead ∨ Cont tailRead C sealRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg ∧ hsame row sealRead)
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
        intro _row other sameRows source
        have otherSame : hsame other sealRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, sealPkg, source.left⟩
  }
  exact ⟨cert, tailUnary, sealUnary, tailRoute, sealRoute⟩

end BEDC.Derived.ContractionMappingUp
