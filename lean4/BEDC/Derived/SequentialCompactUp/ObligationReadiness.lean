import BEDC.Derived.SequentialCompactUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SequentialCompactCarrier [AskSetup] [PackageSetup]
    (compact baire stream window regular realSeal transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  UnaryHistory compact ∧ UnaryHistory baire ∧ UnaryHistory stream ∧ UnaryHistory window ∧
    UnaryHistory regular ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont compact baire stream ∧ Cont stream window regular ∧
          Cont regular realSeal transport ∧ Cont transport replay provenance ∧
            PkgSig bundle provenance pkg

theorem SequentialCompactCarrier_obligation_readiness [AskSetup] [PackageSetup]
    {compact baire stream window regular realSeal transport replay provenance localName
      sourceRead subsequenceRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier compact baire stream window regular realSeal transport replay
        provenance localName bundle pkg →
      Cont compact stream sourceRead →
        Cont sourceRead window subsequenceRead →
          Cont subsequenceRead regular regularRead →
            Cont regularRead realSeal sealRead →
              PkgSig bundle sealRead pkg →
                UnaryHistory compact ∧ UnaryHistory baire ∧ UnaryHistory stream ∧
                  UnaryHistory window ∧ UnaryHistory regular ∧ UnaryHistory realSeal ∧
                    UnaryHistory sourceRead ∧ UnaryHistory subsequenceRead ∧
                      UnaryHistory regularRead ∧ UnaryHistory sealRead ∧
                        Cont compact stream sourceRead ∧
                          Cont sourceRead window subsequenceRead ∧
                            Cont subsequenceRead regular regularRead ∧
                              Cont regularRead realSeal sealRead ∧ PkgSig bundle provenance pkg ∧
                                PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier sourceRoute subsequenceRoute regularRoute sealRoute sealPkg
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed carrier.left carrier.right.right.left sourceRoute
  have subsequenceUnary : UnaryHistory subsequenceRead :=
    unary_cont_closed sourceUnary carrier.right.right.right.left subsequenceRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed subsequenceUnary carrier.right.right.right.right.left regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary carrier.right.right.right.right.right.left sealRoute
  exact
    ⟨carrier.left,
      carrier.right.left,
      carrier.right.right.left,
      carrier.right.right.right.left,
      carrier.right.right.right.right.left,
      carrier.right.right.right.right.right.left,
      sourceUnary,
      subsequenceUnary,
      regularReadUnary,
      sealUnary,
      sourceRoute,
      subsequenceRoute,
      regularRoute,
      sealRoute,
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right,
      sealPkg⟩

theorem SequentialCompactCarrier_window_transport [AskSetup] [PackageSetup]
    {K B S W R E H C P N transportedStream transportedWindow terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont H S transportedStream ->
        Cont transportedStream W transportedWindow ->
          Cont transportedWindow R terminalRead ->
            PkgSig bundle terminalRead pkg ->
              SemanticNameCert
                (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
                    hsame row H ∨ hsame row transportedWindow ∨ hsame row terminalRead)
                (fun row : BHist =>
                  hsame row terminalRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle terminalRead pkg)
                hsame ∧ UnaryHistory transportedStream ∧ UnaryHistory transportedWindow ∧
                  UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro carrier streamRoute windowRoute terminalRoute terminalPkg
  obtain ⟨_kUnary, _bUnary, sUnary, wUnary, rUnary, _eUnary, hUnary,
    _cUnary, _pUnary, _nUnary, _compactBaireStream, _streamWindowRegular,
    _regularSealTransport, _transportReplayProvenance, provenancePkg⟩ := carrier
  have transportedStreamUnary : UnaryHistory transportedStream :=
    unary_cont_closed hUnary sUnary streamRoute
  have transportedWindowUnary : UnaryHistory transportedWindow :=
    unary_cont_closed transportedStreamUnary wUnary windowRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed transportedWindowUnary rUnary terminalRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
            hsame row transportedWindow ∨ hsame row terminalRead)
        (fun row : BHist =>
          hsame row terminalRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle terminalRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalRead ⟨hsame_refl terminalRead, terminalReadUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, provenancePkg, terminalPkg⟩
  }
  exact ⟨cert, transportedStreamUnary, transportedWindowUnary, terminalReadUnary⟩

theorem SequentialCompact_root_obligation_baire_window [AskSetup] [PackageSetup]
    {K B S W R E H C P N selectedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont B W selectedRead ->
        PkgSig bundle selectedRead pkg ->
          UnaryHistory B ∧ UnaryHistory W ∧ UnaryHistory selectedRead ∧
            Cont B W selectedRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle selectedRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier selectedRoute selectedPkg
  obtain ⟨_kUnary, bUnary, _sUnary, wUnary, _rUnary, _eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, provenancePkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed bUnary wUnary selectedRoute
  exact ⟨bUnary, wUnary, selectedUnary, selectedRoute, provenancePkg, selectedPkg⟩

theorem SequentialCompactCarrier_root_obligation_real_seal [AskSetup] [PackageSetup]
    {K B S W R E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row (append E H) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row H ∨ hsame row (append E H) ∨ hsame row P)
          (fun row : BHist =>
            hsame row (append E H) ∧ Cont E H (append E H) ∧ PkgSig bundle P pkg)
          hsame ∧ UnaryHistory (append E H) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier
  obtain ⟨_kUnary, _bUnary, _sUnary, _wUnary, _rUnary, eUnary, hUnary,
    _cUnary, _pUnary, _nUnary, _compactBaireStream, _streamWindowRegular,
    _regularSealTransport, _transportReplayProvenance, provenancePkg⟩ := carrier
  have sealTransport : Cont E H (append E H) := rfl
  have sealUnary : UnaryHistory (append E H) :=
    unary_cont_closed eUnary hUnary sealTransport
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row (append E H) ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row E ∨ hsame row H ∨ hsame row (append E H) ∨ hsame row P)
        (fun row : BHist =>
          hsame row (append E H) ∧ Cont E H (append E H) ∧ PkgSig bundle P pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro (append E H) ⟨hsame_refl (append E H), sealUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inl sourceRow.left))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, sealTransport, provenancePkg⟩
  }
  exact ⟨cert, sealUnary⟩

theorem SequentialCompactCarrier_root_obligation_nonescape [AskSetup] [PackageSetup]
    {K B S W R E H C P N rootRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont K B rootRead ->
        PkgSig bundle rootRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
                  hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                    hsame row rootRead)
              (fun row : BHist =>
                hsame row rootRead ∧ Cont K B rootRead ∧ PkgSig bundle rootRead pkg ∧
                  PkgSig bundle P pkg)
              hsame ∧ UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier rootRoute rootPkg
  obtain ⟨kUnary, bUnary, _sUnary, _wUnary, _rUnary, _eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed kUnary bUnary rootRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
            hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
              hsame row rootRead)
        (fun row : BHist =>
          hsame row rootRead ∧ Cont K B rootRead ∧ PkgSig bundle rootRead pkg ∧
            PkgSig bundle P pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro rootRead ⟨hsame_refl rootRead, rootUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr sourceRow.left)))))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, rootRoute, rootPkg, provenancePkg⟩
  }
  exact ⟨cert, rootUnary⟩

theorem SequentialCompactCarrier_regseqrat_readback_route [AskSetup] [PackageSetup]
    {K B S W R E H C P N selectedRead regularRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg →
      Cont S W selectedRead →
        Cont selectedRead R regularRead →
          Cont regularRead E terminalRead →
            PkgSig bundle terminalRead pkg →
              UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory E ∧
                UnaryHistory selectedRead ∧ UnaryHistory regularRead ∧
                  UnaryHistory terminalRead ∧ Cont S W selectedRead ∧
                    Cont selectedRead R regularRead ∧
                      Cont regularRead E terminalRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier selectedRoute regularRoute terminalRoute terminalPkg
  obtain ⟨_kUnary, _bUnary, sUnary, wUnary, rUnary, eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, provenancePkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed sUnary wUnary selectedRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed selectedUnary rUnary regularRoute
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed regularReadUnary eUnary terminalRoute
  exact
    ⟨wUnary, rUnary, eUnary, selectedUnary, regularReadUnary, terminalReadUnary,
      selectedRoute, regularRoute, terminalRoute, provenancePkg, terminalPkg⟩

theorem SequentialCompactRegSeqRatHandoffExactness [AskSetup] [PackageSetup]
    {K B S W R E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      SemanticNameCert
          (fun row : BHist => hsame row (append (append W R) E) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row P ∨ hsame row N ∨
              hsame row (append W R) ∨ hsame row (append (append W R) E))
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R (append W R) ∧
              Cont (append W R) E (append (append W R) E) ∧ PkgSig bundle P pkg)
          hsame ∧
        UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory (append W R) ∧
          UnaryHistory (append (append W R) E) ∧ Cont W R (append W R) ∧
            Cont (append W R) E (append (append W R) E) ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  intro carrier
  obtain ⟨_kUnary, _bUnary, _sUnary, wUnary, rUnary, eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, provenancePkg⟩ := carrier
  have wrRoute : Cont W R (append W R) := rfl
  have wreRoute : Cont (append W R) E (append (append W R) E) := rfl
  have wrUnary : UnaryHistory (append W R) :=
    unary_cont_closed wUnary rUnary wrRoute
  have wreUnary : UnaryHistory (append (append W R) E) :=
    unary_cont_closed wrUnary eUnary wreRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row (append (append W R) E) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row P ∨ hsame row N ∨
              hsame row (append W R) ∨ hsame row (append (append W R) E))
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W R (append W R) ∧
              Cont (append W R) E (append (append W R) E) ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro (append (append W R) E)
          ⟨hsame_refl (append (append W R) E), wreUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, wrRoute, wreRoute, provenancePkg⟩
  }
  exact
    ⟨cert, wUnary, rUnary, eUnary, wrUnary, wreUnary, wrRoute, wreRoute,
      provenancePkg⟩

end BEDC.Derived.SequentialCompactUp
