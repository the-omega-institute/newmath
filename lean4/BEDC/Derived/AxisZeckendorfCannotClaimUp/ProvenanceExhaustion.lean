import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_provenance_exhaustion [AskSetup] [PackageSetup]
    {a b c d e f g h p n publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg →
      Cont h p publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row p ∨ hsame row n) ∧
                  AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg)
              (fun row : BHist => UnaryHistory row ∧ (hsame row p ∨ hsame row n))
              (fun _row : BHist =>
                Cont h p publicRead ∧ hsame p n ∧
                  PkgSig bundle p pkg ∧ PkgSig bundle publicRead pkg)
              hsame ∧
            UnaryHistory publicRead ∧ Cont h p publicRead ∧ hsame p n ∧
              PkgSig bundle p pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro packet hProvenancePublic publicPkg
  have packetWitness := packet
  obtain
    ⟨aUnary, bUnary, _cUnary, _dUnary, _eUnary, _fUnary, _gUnary, routeAB, _routeCD,
      _routeEF, pUnary, sameProvenanceName, provenancePkg⟩ := packet
  have hUnary : UnaryHistory h :=
    unary_cont_closed aUnary bUnary routeAB
  have nUnary : UnaryHistory n :=
    unary_transport pUnary sameProvenanceName
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed hUnary pUnary hProvenancePublic
  have certCore :
      NameCert
        (fun row : BHist =>
          (hsame row p ∨ hsame row n) ∧
            AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg)
        hsame := by
    exact {
      carrier_inhabited := Exists.intro p
        (And.intro (Or.inl (hsame_refl p)) packetWitness)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same sourceRow
        have sameOtherRow : hsame other row := hsame_symm same
        have otherSource : hsame other p ∨ hsame other n := by
          cases sourceRow.left with
          | inl sameRowP =>
              exact Or.inl (hsame_trans sameOtherRow sameRowP)
          | inr sameRowN =>
              exact Or.inr (hsame_trans sameOtherRow sameRowN)
        exact And.intro otherSource sourceRow.right
    }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row p ∨ hsame row n) ∧
              AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg)
          (fun row : BHist => UnaryHistory row ∧ (hsame row p ∨ hsame row n))
          (fun _row : BHist =>
            Cont h p publicRead ∧ hsame p n ∧
              PkgSig bundle p pkg ∧ PkgSig bundle publicRead pkg)
          hsame := by
    exact {
      core := certCore
      pattern_sound := by
        intro row sourceRow
        have rowUnary : UnaryHistory row := by
          cases sourceRow.left with
          | inl sameRowP =>
              exact unary_transport_symm pUnary sameRowP
          | inr sameRowN =>
              exact unary_transport_symm nUnary sameRowN
        exact And.intro rowUnary sourceRow.left
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨hProvenancePublic, sameProvenanceName, provenancePkg, publicPkg⟩
    }
  exact
    ⟨semantic, publicUnary, hProvenancePublic, sameProvenanceName, provenancePkg,
      publicPkg⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
