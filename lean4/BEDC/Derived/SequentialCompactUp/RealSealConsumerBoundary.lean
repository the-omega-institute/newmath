import BEDC.Derived.SequentialCompactUp.RealSealNonescape

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactRealSealConsumerBoundary [AskSetup] [PackageSetup]
    {K B S W R E H C P N windowRead regularRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont S W windowRead ->
        Cont windowRead R regularRead ->
          Cont regularRead E realRead ->
            PkgSig bundle realRead pkg ->
              SemanticNameCert
                (fun row : BHist => hsame row realRead ∧ UnaryHistory row ∧
                  PkgSig bundle row pkg)
                (fun row : BHist =>
                  hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨
                    hsame row R ∨ hsame row E ∨ hsame row realRead)
                (fun row : BHist =>
                  hsame row realRead ∧ Cont S W windowRead ∧
                    Cont windowRead R regularRead ∧ Cont regularRead E realRead ∧
                      PkgSig bundle realRead pkg)
                hsame ∧ UnaryHistory windowRead ∧ UnaryHistory regularRead ∧
                  UnaryHistory realRead := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute regularRoute realRoute realPkg
  obtain ⟨_kUnary, _bUnary, sUnary, wUnary, rUnary, eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, _provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sUnary wUnary windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary rUnary regularRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary eUnary realRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row realRead ∧ UnaryHistory row ∧
          PkgSig bundle row pkg)
        (fun row : BHist =>
          hsame row K ∨ hsame row B ∨ hsame row S ∨ hsame row W ∨ hsame row R ∨
            hsame row E ∨ hsame row realRead)
        (fun row : BHist =>
          hsame row realRead ∧ Cont S W windowRead ∧ Cont windowRead R regularRead ∧
            Cont regularRead E realRead ∧ PkgSig bundle realRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead
        ⟨hsame_refl realRead, realUnary, realPkg⟩
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
        intro _row other sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, windowRoute, regularRoute, realRoute, realPkg⟩
  }
  exact ⟨cert, windowUnary, regularUnary, realUnary⟩

theorem SequentialCompactRealSealConsumerNonescapeCertificate [AskSetup] [PackageSetup]
    {K B S W R E H C P N windowRead regularRead realRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont S W windowRead ->
        Cont windowRead R regularRead ->
          Cont regularRead E realRead ->
            Cont realRead N namedRead ->
              PkgSig bundle realRead pkg ->
                PkgSig bundle namedRead pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
                        hsame row realRead ∨ hsame row namedRead)
                    (fun row : BHist =>
                      hsame row namedRead ∧ Cont S W windowRead ∧
                        Cont windowRead R regularRead ∧ Cont regularRead E realRead ∧
                          Cont realRead N namedRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle realRead pkg ∧ PkgSig bundle namedRead pkg)
                    hsame ∧ UnaryHistory windowRead ∧ UnaryHistory regularRead ∧
                    UnaryHistory realRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier_real_seal_nonescape SemanticNameCert
  intro carrier windowRoute regularRoute realRoute namedRoute realPkg namedPkg
  have sealFacts :
      UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory E ∧
        UnaryHistory windowRead ∧ UnaryHistory regularRead ∧ UnaryHistory realRead ∧
          Cont S W windowRead ∧ Cont windowRead R regularRead ∧
            Cont regularRead E realRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle realRead pkg :=
    SequentialCompactCarrier_real_seal_nonescape
      (K := K) (B := B) (S := S) (W := W) (R := R) (E := E) (H := H) (C := C)
      (P := P) (N := N) (selectedRead := windowRead) (regularRead := regularRead)
      (sealRead := realRead) (bundle := bundle) (pkg := pkg)
      carrier windowRoute regularRoute realRoute realPkg
  obtain ⟨_sUnary, _wUnary, _rUnary, _eUnary, windowUnary, regularUnary, realUnary,
    windowRouteFromSeal, regularRouteFromSeal, realRouteFromSeal, provenancePkg,
    realPkgFromSeal⟩ := sealFacts
  obtain ⟨_kCarrierUnary, _bCarrierUnary, _sCarrierUnary, _wCarrierUnary,
    _rCarrierUnary, _eCarrierUnary, _hCarrierUnary, _cCarrierUnary,
    _pCarrierUnary, nUnary, _compactBaireStream, _streamWindowRegular,
    _regularSealTransport, _transportReplayProvenance, _carrierProvenancePkg⟩ :=
    carrier
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary nUnary namedRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row S ∨ hsame row W ∨ hsame row R ∨ hsame row E ∨
            hsame row realRead ∨ hsame row namedRead)
        (fun row : BHist =>
          hsame row namedRead ∧ Cont S W windowRead ∧ Cont windowRead R regularRead ∧
            Cont regularRead E realRead ∧ Cont realRead N namedRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg ∧
                PkgSig bundle namedRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, windowRouteFromSeal, regularRouteFromSeal, realRouteFromSeal,
          namedRoute, provenancePkg, realPkgFromSeal, namedPkg⟩
  }
  exact ⟨cert, windowUnary, regularUnary, realUnary, namedUnary⟩

end BEDC.Derived.SequentialCompactUp
