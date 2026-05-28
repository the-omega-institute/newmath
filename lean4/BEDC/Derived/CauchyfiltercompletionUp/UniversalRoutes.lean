import BEDC.Derived.CauchyfiltercompletionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionRootUniformRoute [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name uniformRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont sealRow transport uniformRead →
        PkgSig bundle uniformRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                  hsame row readback ∨ hsame row sealRow ∨ hsame row uniformRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle uniformRead pkg ∧
                  Cont sealRow transport uniformRead)
              hsame ∧
            UnaryHistory uniformRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet uniformRoute uniformPkg
  obtain ⟨_filterUnary, _windowsUnary, _toleranceUnary, _readbackUnary, sealUnary,
    transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _filterWindows,
    _toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed sealUnary transportUnary uniformRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row uniformRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle uniformRead pkg ∧
              Cont sealRow transport uniformRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead
          ⟨hsame_refl uniformRead, uniformUnary⟩
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
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.right, uniformPkg, uniformRoute⟩
    }
  exact ⟨cert, uniformUnary, provenancePkg⟩

theorem CauchyFilterCompletionBasisUniversalConsumerRoute [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name basisRead
      universalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont readback sealRow basisRead →
        Cont basisRead provenance universalRead →
          PkgSig bundle universalRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row universalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                    hsame row readback ∨ hsame row sealRow ∨ hsame row basisRead ∨
                      hsame row universalRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle universalRead pkg ∧
                    Cont basisRead provenance universalRead)
                hsame ∧
              UnaryHistory basisRead ∧ UnaryHistory universalRead ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet basisRoute universalRoute universalPkg
  obtain ⟨_filterUnary, _windowsUnary, _toleranceUnary, readbackUnary, sealUnary,
    _transportUnary, _replayUnary, provenanceUnary, _nameUnary, _filterWindows,
    _toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have basisUnary : UnaryHistory basisRead :=
    unary_cont_closed readbackUnary sealUnary basisRoute
  have universalUnary : UnaryHistory universalRead :=
    unary_cont_closed basisUnary provenanceUnary universalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row universalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
              hsame row readback ∨ hsame row sealRow ∨ hsame row basisRead ∨
                hsame row universalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle universalRead pkg ∧
              Cont basisRead provenance universalRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro universalRead
          ⟨hsame_refl universalRead, universalUnary⟩
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
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              unary_transport source.right sameRows⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
      ledger_sound := by
        intro _row source
        exact ⟨source.right, universalPkg, universalRoute⟩
    }
  exact ⟨cert, basisUnary, universalUnary, provenancePkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
