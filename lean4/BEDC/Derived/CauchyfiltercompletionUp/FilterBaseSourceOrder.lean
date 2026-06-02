import BEDC.Derived.CauchyfiltercompletionUp

namespace BEDC.Derived.CauchyfiltercompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyFilterCompletionPacket_filter_base_source_order [AskSetup] [PackageSetup]
    {filter windows tolerance readback sealRow transport replay provenance name sourceRead
      filterbaseRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCompletionPacket filter windows tolerance readback sealRow transport replay
        provenance name bundle pkg →
      Cont filter windows sourceRead →
        Cont sourceRead tolerance filterbaseRead →
          Cont filterbaseRead readback completionRead →
            PkgSig bundle completionRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row sourceRead ∨ hsame row filterbaseRead ∨
                        hsame row completionRead) ∧
                      UnaryHistory row)
                  (fun row : BHist =>
                    hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
                      hsame row readback ∨ hsame row sourceRead ∨
                        hsame row filterbaseRead ∨ hsame row completionRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont sourceRead tolerance filterbaseRead ∧
                      Cont filterbaseRead readback completionRead ∧
                        PkgSig bundle completionRead pkg)
                  hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory filterbaseRead ∧
                  UnaryHistory completionRead ∧ Cont filter windows tolerance ∧
                    Cont tolerance readback sealRow ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet sourceRoute filterbaseRoute completionRoute completionPkg
  obtain ⟨filterUnary, windowsUnary, toleranceUnary, readbackUnary, _sealUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, filterWindows,
    toleranceReadback, _transportReplay, provenancePkg, _namePkg⟩ := packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed filterUnary windowsUnary sourceRoute
  have filterbaseUnary : UnaryHistory filterbaseRead :=
    unary_cont_closed sourceUnary toleranceUnary filterbaseRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed filterbaseUnary readbackUnary completionRoute
  have sourceSource :
      (fun row : BHist =>
        (hsame row sourceRead ∨ hsame row filterbaseRead ∨ hsame row completionRead) ∧
          UnaryHistory row) sourceRead := by
    exact ⟨Or.inl (hsame_refl sourceRead), sourceUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row sourceRead ∨ hsame row filterbaseRead ∨
                hsame row completionRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row filter ∨ hsame row windows ∨ hsame row tolerance ∨
              hsame row readback ∨ hsame row sourceRead ∨ hsame row filterbaseRead ∨
                hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont sourceRead tolerance filterbaseRead ∧
              Cont filterbaseRead readback completionRead ∧ PkgSig bundle completionRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead sourceSource
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
        constructor
        · cases source.left with
          | inl sameSource =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameSource)
          | inr rest =>
              cases rest with
              | inl sameFilterbase =>
                  exact
                    Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameFilterbase))
              | inr sameCompletion =>
                  exact
                    Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameCompletion))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSource =>
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl sameSource
      | inr rest =>
          cases rest with
          | inl sameFilterbase =>
              exact
                Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                  Or.inl sameFilterbase
          | inr sameCompletion =>
              exact
                Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
                  Or.inr sameCompletion
    ledger_sound := by
      intro _row source
      exact ⟨source.right, filterbaseRoute, completionRoute, completionPkg⟩
  }
  exact
    ⟨cert, sourceUnary, filterbaseUnary, completionUnary, filterWindows, toleranceReadback,
      provenancePkg⟩

end BEDC.Derived.CauchyfiltercompletionUp
