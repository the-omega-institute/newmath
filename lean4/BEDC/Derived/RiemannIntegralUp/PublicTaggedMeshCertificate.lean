import BEDC.Derived.RiemannIntegralUp

namespace BEDC.Derived.RiemannIntegralUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RiemannIntegralPacket_public_tagged_mesh_certificate [AskSetup] [PackageSetup]
    {M T F S D G R H C P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RiemannIntegralPacket M T F S D G R H C P N bundle pkg →
      Cont R H publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row T ∨ hsame row F ∨ hsame row S ∨
                  hsame row D ∨ hsame row G ∨ hsame row R ∨ Cont R H publicRead)
              (fun row : BHist =>
                PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg ∧ hsame row publicRead)
              hsame ∧
            UnaryHistory publicRead ∧ Cont R H publicRead ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet realPublic publicPkg
  obtain ⟨mUnary, _tUnary, _fUnary, _sUnary, _dUnary, _gUnary, rUnary, hUnary,
    _cUnary, _pUnary, _nUnary, _mtf, _fsd, _dgr, provenancePkg, _namePkg⟩ := packet
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed rUnary hUnary realPublic
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row T ∨ hsame row F ∨ hsame row S ∨ hsame row D ∨
              hsame row G ∨ hsame row R ∨ Cont R H publicRead)
          (fun row : BHist =>
            PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg ∧ hsame row publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
        have otherSame : hsame other publicRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        exact ⟨otherSame, otherUnary⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr realPublic))))))
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, publicPkg, source.left⟩
  }
  exact ⟨cert, publicUnary, realPublic, publicPkg⟩

end BEDC.Derived.RiemannIntegralUp
