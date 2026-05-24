import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessPacket_ledger_boundary [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports routes
        provenance name bundle pkg →
      Cont pole zeroLedger gamma →
      Cont routes name ledgerRead →
      UnaryHistory routes →
      UnaryHistory name →
      PkgSig bundle ledgerRead pkg →
      SemanticNameCert
          (fun row : BHist =>
            ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
              transports routes provenance name bundle pkg ∧
              (hsame row pole ∨ hsame row zeroLedger ∨ hsame row gamma ∨
                hsame row ledgerRead))
          (fun row : BHist =>
            hsame row pole ∨ hsame row zeroLedger ∨ hsame row gamma ∨ hsame row ledgerRead)
          (fun _row : BHist => PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg)
          hsame ∧
        UnaryHistory ledgerRead ∧ hsame ledgerRead (append routes name) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet poleLedgerGamma routesNameRead routesUnary nameUnary ledgerReadPkg
  have packetKeep := packet
  obtain ⟨_basicAnalytic, _analyticTransport, _poleGamma, _transportProvenance, _namePkg,
    provenancePkg⟩ := packet
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed routesUnary nameUnary routesNameRead
  have sourcePole :
      (fun row : BHist =>
        ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
          transports routes provenance name bundle pkg ∧
          (hsame row pole ∨ hsame row zeroLedger ∨ hsame row gamma ∨ hsame row ledgerRead))
        pole := by
    exact ⟨packetKeep, Or.inl (hsame_refl pole)⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma
              transports routes provenance name bundle pkg ∧
              (hsame row pole ∨ hsame row zeroLedger ∨ hsame row gamma ∨
                hsame row ledgerRead))
          (fun row : BHist =>
            hsame row pole ∨ hsame row zeroLedger ∨ hsame row gamma ∨ hsame row ledgerRead)
          (fun _row : BHist => PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro pole sourcePole
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
          rcases source with ⟨packetSource, rowMembership⟩
          have moveToOther :
              hsame other pole ∨ hsame other zeroLedger ∨ hsame other gamma ∨
                hsame other ledgerRead := by
            cases rowMembership with
            | inl rowPole =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) rowPole)
            | inr rest =>
                cases rest with
                | inl rowZero =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowZero))
                | inr rest' =>
                    cases rest' with
                    | inl rowGamma =>
                        exact Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowGamma)))
                    | inr rowLedger =>
                        exact Or.inr
                          (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) rowLedger)))
          exact ⟨packetSource, moveToOther⟩
      }
      pattern_sound := by
        intro _row source
        exact source.right
      ledger_sound := by
        intro _row _source
        exact ⟨provenancePkg, ledgerReadPkg⟩
    }
  exact ⟨cert, ledgerUnary, routesNameRead⟩

theorem ZetaContinuationWitnessCarrier_ledger_nonescape_boundary [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
        routes provenance name bundle pkg ->
      UnaryHistory routes ->
        UnaryHistory name ->
          Cont routes name ledgerRead ->
            UnaryHistory ledgerRead ∧ hsame ledgerRead (append routes name) ∧
              Cont transports routes provenance ∧ PkgSig bundle name pkg ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet routesUnary nameUnary routesNameLedger
  obtain ⟨_basicEtaAnalytic, _analyticFunctionalTransports, _poleZeroLedgerGamma,
    transportsRoutesProvenance, namePkg, provenancePkg⟩ := packet
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed routesUnary nameUnary routesNameLedger
  exact
    ⟨ledgerReadUnary, routesNameLedger, transportsRoutesProvenance, namePkg,
      provenancePkg⟩

end BEDC.Derived.ZetaContinuationWitnessUp
