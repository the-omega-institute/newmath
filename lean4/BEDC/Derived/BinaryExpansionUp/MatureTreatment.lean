import BEDC.Derived.BinaryExpansionUp

namespace BEDC.Derived.BinaryExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BinaryExpansionPacket_mature_treatment [AskSetup] [PackageSetup]
    {digits windows approximation regular realSeal transport route provenance nameCert bridgeRead
      publicRead modulusRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BinaryExpansionPacket digits windows approximation regular realSeal transport route provenance
        nameCert bundle pkg →
      Cont windows approximation bridgeRead →
        Cont bridgeRead regular realSeal →
          Cont windows approximation modulusRead →
            Cont modulusRead realSeal sealRead →
              Cont bridgeRead realSeal publicRead →
                PkgSig bundle bridgeRead pkg →
                  PkgSig bundle modulusRead pkg →
                    PkgSig bundle sealRead pkg →
                      PkgSig bundle publicRead pkg →
                        SemanticNameCert
                            (fun row : BHist =>
                              hsame row realSeal ∨ hsame row bridgeRead ∨
                                hsame row publicRead)
                            (fun row : BHist => UnaryHistory row)
                            (fun _row : BHist =>
                              PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
                                PkgSig bundle sealRead pkg)
                            hsame ∧
                          UnaryHistory bridgeRead ∧ UnaryHistory modulusRead ∧
                            UnaryHistory sealRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet windowsApproximationBridge _bridgeRegularSeal windowsApproximationModulus
    modulusSeal bridgePublic _bridgePkg _modulusPkg sealPkg publicPkg
  obtain ⟨_digitsUnary, windowsUnary, approximationUnary, _regularUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameCertUnary, _windowsDigits,
    _approximationRegular, _transportRoute, provenancePkg⟩ := packet
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed windowsUnary approximationUnary windowsApproximationBridge
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed windowsUnary approximationUnary windowsApproximationModulus
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed modulusUnary realSealUnary modulusSeal
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed bridgeUnary realSealUnary bridgePublic
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row realSeal ∨ hsame row bridgeRead ∨ hsame row publicRead)
          (fun row : BHist => UnaryHistory row)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
              PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal (Or.inl (hsame_refl realSeal))
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
        cases source with
        | inl sameSeal =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameSeal)
        | inr tail =>
            cases tail with
            | inl sameBridge =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameBridge))
            | inr samePublic =>
                exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) samePublic))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameSeal =>
          exact unary_transport realSealUnary (hsame_symm sameSeal)
      | inr tail =>
          cases tail with
          | inl sameBridge =>
              exact unary_transport bridgeUnary (hsame_symm sameBridge)
          | inr samePublic =>
              exact unary_transport publicUnary (hsame_symm samePublic)
    ledger_sound := by
      intro _row _source
      exact ⟨provenancePkg, publicPkg, sealPkg⟩
  }
  exact ⟨cert, bridgeUnary, modulusUnary, sealUnary, publicUnary⟩

end BEDC.Derived.BinaryExpansionUp
