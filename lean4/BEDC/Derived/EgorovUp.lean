import BEDC.Derived.EgorovUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EgorovUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def EgorovCarrier [AskSetup] [PackageSetup]
    (measure prob family limit schedule readback exceptional window uniformity ledger transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  (∃ packet : EgorovUp,
      packet =
        EgorovUp.mk measure prob family limit schedule readback exceptional window uniformity ledger
          transport replay provenance localName) ∧
    UnaryHistory measure ∧ UnaryHistory prob ∧ UnaryHistory family ∧ UnaryHistory limit ∧
      UnaryHistory schedule ∧ UnaryHistory readback ∧ UnaryHistory exceptional ∧
        UnaryHistory window ∧ UnaryHistory uniformity ∧ UnaryHistory ledger ∧
          UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
            UnaryHistory localName ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem EgorovCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {measure prob family limit schedule readback exceptional window uniformity ledger transport replay
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EgorovCarrier measure prob family limit schedule readback exceptional window uniformity ledger
        transport replay provenance localName bundle pkg ->
      Cont exceptional window uniformity ->
        Cont uniformity ledger replay ->
          PkgSig bundle provenance pkg ->
            SemanticNameCert
                  (fun row : BHist => hsame row uniformity ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row exceptional ∨ hsame row window ∨ hsame row uniformity ∨
                      hsame row ledger)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont exceptional window uniformity ∧
                      Cont uniformity ledger replay ∧ PkgSig bundle provenance pkg)
                  hsame ∧
              UnaryHistory exceptional ∧ UnaryHistory window ∧ UnaryHistory uniformity ∧
                UnaryHistory ledger := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier exceptionalWindowRoute uniformityLedgerRoute provenancePkg
  obtain ⟨_packetWitness, _measureUnary, _probUnary, _familyUnary, _limitUnary,
    _scheduleUnary, _readbackUnary, exceptionalUnary, windowUnary, uniformityUnary,
    ledgerUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _provenancePkgCarrier, _localNamePkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformity ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row exceptional ∨ hsame row window ∨ hsame row uniformity ∨
              hsame row ledger)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont exceptional window uniformity ∧
              Cont uniformity ledger replay ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro uniformity ⟨hsame_refl uniformity, uniformityUnary⟩
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
      exact Or.inr (Or.inr (Or.inl source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, exceptionalWindowRoute, uniformityLedgerRoute, provenancePkg⟩
  }
  exact ⟨cert, exceptionalUnary, windowUnary, uniformityUnary, ledgerUnary⟩

theorem Egorov_exceptional_set_ledger_exposure [AskSetup] [PackageSetup]
    {M Omega F X S R A W U L H C P N exceptionalRead ledgerRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EgorovCarrier M Omega F X S R A W U L H C P N bundle pkg ->
      Cont A L exceptionalRead ->
        Cont exceptionalRead H ledgerRead ->
          Cont ledgerRead C consumerRead ->
            PkgSig bundle P pkg ->
              SemanticNameCert
                    (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row Omega ∨ hsame row A ∨ hsame row L ∨
                        hsame row exceptionalRead ∨ hsame row ledgerRead ∨
                          hsame row consumerRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont A L exceptionalRead ∧
                        Cont exceptionalRead H ledgerRead ∧ Cont ledgerRead C consumerRead ∧
                          PkgSig bundle P pkg)
                    hsame ∧
                UnaryHistory exceptionalRead ∧ UnaryHistory ledgerRead ∧
                  UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier exceptionalRoute ledgerRoute consumerRoute provenancePkg
  obtain ⟨_packetWitness, _measureUnary, _probUnary, _familyUnary, _limitUnary,
    _scheduleUnary, _readbackUnary, exceptionalUnary, _windowUnary, _uniformityUnary,
    ledgerUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _provenancePkgCarrier, _localNamePkg⟩ := carrier
  have exceptionalReadUnary : UnaryHistory exceptionalRead :=
    unary_cont_closed exceptionalUnary ledgerUnary exceptionalRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed exceptionalReadUnary _transportUnary ledgerRoute
  have consumerReadUnary : UnaryHistory consumerRead :=
    unary_cont_closed ledgerReadUnary _replayUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Omega ∨ hsame row A ∨ hsame row L ∨
              hsame row exceptionalRead ∨ hsame row ledgerRead ∨ hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A L exceptionalRead ∧
              Cont exceptionalRead H ledgerRead ∧ Cont ledgerRead C consumerRead ∧
                PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead
        ⟨hsame_refl consumerRead, consumerReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, exceptionalRoute, ledgerRoute, consumerRoute, provenancePkg⟩
  }
  exact ⟨cert, exceptionalReadUnary, ledgerReadUnary, consumerReadUnary⟩

theorem Egorov_streamname_real_uniform_window_handoff [AskSetup] [PackageSetup]
    {M Omega F X S R A W U L H C P N streamRead toleranceRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EgorovCarrier M Omega F X S R A W U L H C P N bundle pkg ->
      Cont S R streamRead ->
        Cont streamRead W toleranceRead ->
          Cont toleranceRead U realRead ->
            PkgSig bundle P pkg ->
              SemanticNameCert
                    (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row R ∨ hsame row W ∨ hsame row U ∨
                        hsame row streamRead ∨ hsame row toleranceRead ∨ hsame row realRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S R streamRead ∧
                        Cont streamRead W toleranceRead ∧ Cont toleranceRead U realRead ∧
                          PkgSig bundle P pkg)
                    hsame ∧
                UnaryHistory streamRead ∧ UnaryHistory toleranceRead ∧
                  UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier streamRoute toleranceRoute realRoute provenancePkg
  obtain ⟨_packetWitness, _measureUnary, _probUnary, _familyUnary, _limitUnary,
    scheduleUnary, readbackUnary, _exceptionalUnary, windowUnary, uniformityUnary,
    _ledgerUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _provenancePkgCarrier, _localNamePkg⟩ := carrier
  have streamReadUnary : UnaryHistory streamRead :=
    unary_cont_closed scheduleUnary readbackUnary streamRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed streamReadUnary windowUnary toleranceRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed toleranceReadUnary uniformityUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row W ∨ hsame row U ∨
              hsame row streamRead ∨ hsame row toleranceRead ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R streamRead ∧
              Cont streamRead W toleranceRead ∧ Cont toleranceRead U realRead ∧
                PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, streamRoute, toleranceRoute, realRoute, provenancePkg⟩
  }
  exact ⟨cert, streamReadUnary, toleranceReadUnary, realReadUnary⟩

end BEDC.Derived.EgorovUp
