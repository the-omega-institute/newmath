import BEDC.Derived.FareySequenceUp.NameCertObligations

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceCarrier_namecert_real_bracket_lock [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N approxRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont B A M ->
        Cont M L S ->
          Cont S T G ->
            Cont G E approxRead ->
              Cont approxRead E sealRead ->
                PkgSig bundle N pkg ->
                  PkgSig bundle sealRead pkg ->
                    SemanticNameCert
                        (fun row : BHist => hsame row approxRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨
                            hsame row T ∨ hsame row S ∨ hsame row G ∨ hsame row E ∨
                              hsame row approxRead ∨ hsame row N)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont B A M ∧ Cont M L S ∧ Cont S T G ∧
                            Cont G E approxRead ∧ PkgSig bundle N pkg)
                        hsame ∧
                      UnaryHistory approxRead ∧ UnaryHistory sealRead ∧
                        Cont approxRead E sealRead ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier boundaryRoute levelRoute toleranceRoute approximationRoute sealRoute namePkg
    sealPkg
  obtain ⟨boundaryUnary, adjacencyUnary, _mediantUnary, levelUnary, toleranceUnary,
    _sternBrocotUnary, _densityUnary, _rationalUnary, _windowUnary, _readbackUnary,
    _approximationCarrierUnary, sealUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _nameUnary, _adjacencyEmpty, _sternBrocotEmpty, _mediantEmpty,
    _approximationEmpty, _sealEmpty, _provenancePkg⟩ := carrier
  obtain ⟨cert, _mediantClosed, _sternBrocotClosed, _approximationClosed,
    approxReadUnary⟩ :=
    FareySequenceCarrier_namecert_obligations
      (B := B) (A := A) (M := M) (L := L) (T := T) (S := S) (D := D) (Q := Q)
      (W := W) (R := R) (G := G) (E := E) (H := H) (C := C) (P := P)
      (N := N) (approxRead := approxRead) (bundle := bundle) (pkg := pkg)
      boundaryUnary adjacencyUnary levelUnary toleranceUnary sealUnary boundaryRoute
      levelRoute toleranceRoute approximationRoute namePkg
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed approxReadUnary sealUnary sealRoute
  exact ⟨cert, approxReadUnary, sealReadUnary, sealRoute, sealPkg⟩

theorem FareySequenceCarrier_real_bracket_consumer_lock [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N boundaryRead mediantRead denomRead
      toleranceRead sternRead rationalRead windowRead readbackRead approximationRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont B A boundaryRead ->
        Cont boundaryRead M mediantRead ->
          Cont mediantRead L denomRead ->
            Cont denomRead T toleranceRead ->
              Cont toleranceRead S sternRead ->
                Cont sternRead Q rationalRead ->
                  Cont rationalRead W windowRead ->
                    Cont windowRead R readbackRead ->
                      Cont readbackRead G approximationRead ->
                        Cont approximationRead E sealRead ->
                          PkgSig bundle sealRead pkg ->
                            SemanticNameCert
                                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row B ∨ hsame row A ∨ hsame row M ∨
                                    hsame row L ∨ hsame row T ∨ hsame row S ∨
                                      hsame row Q ∨ hsame row W ∨ hsame row R ∨
                                        hsame row G ∨ hsame row E ∨ hsame row sealRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ PkgSig bundle sealRead pkg)
                                hsame ∧
                              UnaryHistory boundaryRead ∧ UnaryHistory mediantRead ∧
                                UnaryHistory denomRead ∧ UnaryHistory toleranceRead ∧
                                  UnaryHistory sternRead ∧ UnaryHistory rationalRead ∧
                                    UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                                      UnaryHistory approximationRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier boundaryRoute mediantRoute denomRoute toleranceRoute sternRoute rationalRoute
    windowRoute readbackRoute approximationRoute sealRoute sealPkg
  obtain ⟨bUnary, aUnary, mUnary, lUnary, tUnary, sUnary, _dUnary, qUnary, wUnary,
    rUnary, gUnary, eUnary, _hUnary, _cUnary, _pUnary, _nUnary, _aEmpty, _sEmpty,
    _mEmpty, _gEmpty, _eEmpty, _carrierPkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed bUnary aUnary boundaryRoute
  have mediantUnary : UnaryHistory mediantRead :=
    unary_cont_closed boundaryUnary mUnary mediantRoute
  have denomUnary : UnaryHistory denomRead :=
    unary_cont_closed mediantUnary lUnary denomRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed denomUnary tUnary toleranceRoute
  have sternUnary : UnaryHistory sternRead :=
    unary_cont_closed toleranceUnary sUnary sternRoute
  have rationalUnary : UnaryHistory rationalRead :=
    unary_cont_closed sternUnary qUnary rationalRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed rationalUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have approximationUnary : UnaryHistory approximationRead :=
    unary_cont_closed readbackUnary gUnary approximationRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed approximationUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row A ∨ hsame row M ∨ hsame row L ∨ hsame row T ∨
              hsame row S ∨ hsame row Q ∨ hsame row W ∨ hsame row R ∨ hsame row G ∨
                hsame row E ∨ hsame row sealRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealRead pkg)
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
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
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sealPkg⟩
  }
  exact
    ⟨cert, boundaryUnary, mediantUnary, denomUnary, toleranceUnary, sternUnary,
      rationalUnary, windowUnary, readbackUnary, approximationUnary, sealUnary⟩

end BEDC.Derived.FareySequenceUp
