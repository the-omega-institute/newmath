import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BooleanalgebraUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BooleanAlgebraCarrier [AskSetup] [PackageSetup]
    (join meet compl zero one order transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory join ∧ UnaryHistory meet ∧ UnaryHistory compl ∧ UnaryHistory zero ∧
    UnaryHistory one ∧ UnaryHistory order ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
      UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont join meet order ∧
        Cont compl zero replay ∧ Cont transport replay provenance ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem BooleanAlgebraCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {join meet compl zero one order transport replay provenance localName endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BooleanAlgebraCarrier join meet compl zero one order transport replay provenance localName
        bundle pkg →
      Cont compl zero endpoint →
        Cont endpoint one replay →
          PkgSig bundle endpoint pkg →
            SemanticNameCert
                (fun row : BHist =>
                  BooleanAlgebraCarrier join meet compl zero one order transport replay
                    provenance localName bundle pkg ∧ hsame row endpoint)
                (fun row : BHist =>
                  hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
                    hsame row one ∨ hsame row order ∨ hsame row endpoint)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle endpoint pkg)
                hsame ∧
              UnaryHistory endpoint ∧ Cont join meet order ∧ Cont compl zero endpoint ∧
                Cont endpoint one replay := by
  -- BEDC touchpoint anchor: BooleanAlgebraCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows complZero endpointOne endpointPkg
  obtain ⟨joinUnary, meetUnary, complUnary, zeroUnary, oneUnary, orderUnary,
    transportUnary, replayUnary, provenanceUnary, localNameUnary, joinMeetOrder,
    complZeroReplay, transportReplayProvenance, provenancePkg, localNamePkg⟩ :=
      carrierRows
  have carrierWitness :
      BooleanAlgebraCarrier join meet compl zero one order transport replay provenance
        localName bundle pkg := by
    exact
      ⟨joinUnary, meetUnary, complUnary, zeroUnary, oneUnary, orderUnary, transportUnary,
        replayUnary, provenanceUnary, localNameUnary, joinMeetOrder, complZeroReplay,
        transportReplayProvenance, provenancePkg, localNamePkg⟩
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed complUnary zeroUnary complZero
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            BooleanAlgebraCarrier join meet compl zero one order transport replay provenance
              localName bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
              hsame row one ∨ hsame row order ∨ hsame row endpoint)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint ⟨carrierWitness, hsame_refl endpoint⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.right)))))
    ledger_sound := by
      intro row source
      exact
        ⟨unary_transport endpointUnary (hsame_symm source.right), provenancePkg, endpointPkg⟩
  }
  exact ⟨cert, endpointUnary, joinMeetOrder, complZero, endpointOne⟩

theorem BooleanAlgebraCarrier_stone_duality_forward_route [AskSetup] [PackageSetup]
    {join meet compl zero one order transport replay provenance localName stoneRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BooleanAlgebraCarrier join meet compl zero one order transport replay provenance localName
        bundle pkg →
      Cont order localName stoneRead →
        PkgSig bundle provenance pkg →
          PkgSig bundle stoneRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row stoneRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
                    hsame row one ∨ hsame row order ∨ hsame row stoneRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont order localName stoneRead ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle stoneRead pkg)
                hsame ∧
              UnaryHistory stoneRead := by
  -- BEDC touchpoint anchor: BooleanAlgebraCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows stoneRoute provenancePkg stonePkg
  obtain ⟨joinUnary, meetUnary, complUnary, zeroUnary, oneUnary, orderUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localNameUnary, _joinMeetOrder,
    _complZeroReplay, _transportReplayProvenance, _carrierProvenancePkg,
    _localNamePkg⟩ := carrierRows
  have stoneUnary : UnaryHistory stoneRead :=
    unary_cont_closed orderUnary localNameUnary stoneRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stoneRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
              hsame row one ∨ hsame row order ∨ hsame row stoneRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont order localName stoneRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle stoneRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro stoneRead ⟨hsame_refl stoneRead, stoneUnary⟩
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
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, stoneRoute, provenancePkg, stonePkg⟩
  }
  exact ⟨cert, stoneUnary⟩

theorem BooleanAlgebraCarrier_stone_duality_handoff [AskSetup] [PackageSetup]
    {join meet compl zero one order transport replay provenance localName stoneRead
      handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BooleanAlgebraCarrier join meet compl zero one order transport replay provenance localName
        bundle pkg →
      Cont order localName stoneRead →
        Cont stoneRead provenance handoffRead →
          PkgSig bundle provenance pkg →
            PkgSig bundle handoffRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
                      hsame row one ∨ hsame row order ∨ hsame row stoneRead ∨
                        hsame row handoffRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont order localName stoneRead ∧
                      Cont stoneRead provenance handoffRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg)
                  hsame ∧
                UnaryHistory stoneRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BooleanAlgebraCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows stoneRoute handoffRoute provenancePkg handoffPkg
  obtain ⟨joinUnary, meetUnary, complUnary, zeroUnary, oneUnary, orderUnary,
    _transportUnary, _replayUnary, provenanceUnary, localNameUnary, _joinMeetOrder,
    _complZeroReplay, _transportReplayProvenance, _carrierProvenancePkg,
    _localNamePkg⟩ := carrierRows
  have stoneUnary : UnaryHistory stoneRead :=
    unary_cont_closed orderUnary localNameUnary stoneRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed stoneUnary provenanceUnary handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
              hsame row one ∨ hsame row order ∨ hsame row stoneRead ∨
                hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont order localName stoneRead ∧
              Cont stoneRead provenance handoffRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, stoneRoute, handoffRoute, provenancePkg, handoffPkg⟩
  }
  exact ⟨cert, stoneUnary, handoffUnary⟩

theorem BooleanAlgebraLatticeDependencyRoute [AskSetup] [PackageSetup]
    {join meet compl zero one order transport replay provenance localName latticeRead
      stoneRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BooleanAlgebraCarrier join meet compl zero one order transport replay provenance localName
        bundle pkg →
      Cont join meet latticeRead →
        Cont latticeRead compl stoneRead →
          PkgSig bundle stoneRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row stoneRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
                    hsame row one ∨ hsame row order ∨ hsame row latticeRead ∨
                      hsame row stoneRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont join meet latticeRead ∧
                    Cont latticeRead compl stoneRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle stoneRead pkg)
                hsame ∧
              UnaryHistory latticeRead ∧ UnaryHistory stoneRead := by
  -- BEDC touchpoint anchor: BooleanAlgebraCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows latticeRoute stoneRoute stonePkg
  obtain ⟨joinUnary, meetUnary, complUnary, _zeroUnary, _oneUnary, _orderUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _joinMeetOrder,
    _complZeroReplay, _transportReplayProvenance, provenancePkg, _localNamePkg⟩ :=
      carrierRows
  have latticeUnary : UnaryHistory latticeRead :=
    unary_cont_closed joinUnary meetUnary latticeRoute
  have stoneUnary : UnaryHistory stoneRead :=
    unary_cont_closed latticeUnary complUnary stoneRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stoneRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
              hsame row one ∨ hsame row order ∨ hsame row latticeRead ∨
                hsame row stoneRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont join meet latticeRead ∧
              Cont latticeRead compl stoneRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle stoneRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro stoneRead ⟨hsame_refl stoneRead, stoneUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, latticeRoute, stoneRoute, provenancePkg, stonePkg⟩
  }
  exact ⟨cert, latticeUnary, stoneUnary⟩

theorem BooleanAlgebraStoneDualityHandoff [AskSetup] [PackageSetup]
    {join meet compl zero one order transport replay provenance localName endpoint booleanSource
      stoneRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BooleanAlgebraCarrier join meet compl zero one order transport replay provenance localName
        bundle pkg →
      Cont compl zero endpoint →
        Cont endpoint one booleanSource →
          Cont booleanSource localName stoneRead →
            PkgSig bundle provenance pkg →
              PkgSig bundle localName pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row stoneRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
                        hsame row one ∨ hsame row order ∨ hsame row endpoint ∨
                          hsame row booleanSource ∨ hsame row stoneRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont compl zero endpoint ∧
                        Cont endpoint one booleanSource ∧
                          Cont booleanSource localName stoneRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                    hsame ∧
                  UnaryHistory endpoint ∧ UnaryHistory booleanSource ∧
                    UnaryHistory stoneRead := by
  -- BEDC touchpoint anchor: BooleanAlgebraCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows complZero endpointOne booleanSourceLocalName provenancePkg localNamePkg
  obtain ⟨_joinUnary, _meetUnary, complUnary, zeroUnary, oneUnary, _orderUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localNameUnary, _joinMeetOrder,
    _complZeroReplay, _transportReplayProvenance, _carrierProvenancePkg, _carrierLocalNamePkg⟩ :=
      carrierRows
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed complUnary zeroUnary complZero
  have booleanSourceUnary : UnaryHistory booleanSource :=
    unary_cont_closed endpointUnary oneUnary endpointOne
  have stoneReadUnary : UnaryHistory stoneRead :=
    unary_cont_closed booleanSourceUnary localNameUnary booleanSourceLocalName
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro stoneRead ⟨hsame_refl stoneRead, stoneReadUnary⟩
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
                        (Or.inr source.left)))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, complZero, endpointOne, booleanSourceLocalName, provenancePkg,
            localNamePkg⟩
    }
  · exact ⟨endpointUnary, booleanSourceUnary, stoneReadUnary⟩

theorem BooleanAlgebraDossierLatticeRoute [AskSetup] [PackageSetup]
    {join meet compl zero one order transport replay provenance localName endpoint booleanSource
      stoneRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BooleanAlgebraCarrier join meet compl zero one order transport replay provenance localName
        bundle pkg →
      Cont compl zero endpoint →
        Cont endpoint one booleanSource →
          Cont booleanSource localName stoneRead →
            PkgSig bundle provenance pkg →
              PkgSig bundle localName pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row stoneRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row zero ∨ hsame row one ∨ hsame row meet ∨ hsame row join ∨
                        hsame row compl ∨ hsame row order ∨ hsame row booleanSource ∨
                          hsame row stoneRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont compl zero endpoint ∧
                        Cont endpoint one booleanSource ∧
                          Cont booleanSource localName stoneRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
                    hsame ∧
                  UnaryHistory endpoint ∧ UnaryHistory booleanSource ∧
                    UnaryHistory stoneRead := by
  -- BEDC touchpoint anchor: BooleanAlgebraCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows complZero endpointOne booleanSourceLocalName provenancePkg localNamePkg
  obtain ⟨_joinUnary, meetUnary, complUnary, zeroUnary, oneUnary, _orderUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localNameUnary, _joinMeetOrder,
    _complZeroReplay, _transportReplayProvenance, _carrierProvenancePkg,
    _carrierLocalNamePkg⟩ := carrierRows
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed complUnary zeroUnary complZero
  have booleanSourceUnary : UnaryHistory booleanSource :=
    unary_cont_closed endpointUnary oneUnary endpointOne
  have stoneReadUnary : UnaryHistory stoneRead :=
    unary_cont_closed booleanSourceUnary localNameUnary booleanSourceLocalName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stoneRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row zero ∨ hsame row one ∨ hsame row meet ∨ hsame row join ∨
              hsame row compl ∨ hsame row order ∨ hsame row booleanSource ∨
                hsame row stoneRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compl zero endpoint ∧ Cont endpoint one booleanSource ∧
              Cont booleanSource localName stoneRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro stoneRead ⟨hsame_refl stoneRead, stoneReadUnary⟩
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
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, complZero, endpointOne, booleanSourceLocalName, provenancePkg,
          localNamePkg⟩
  }
  exact ⟨cert, endpointUnary, booleanSourceUnary, stoneReadUnary⟩

theorem BooleanAlgebraCarrier_stone_source_lattice_determinacy [AskSetup] [PackageSetup]
    {join meet compl zero one order transport replay provenance localName endpoint booleanSource
      stoneRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BooleanAlgebraCarrier join meet compl zero one order transport replay provenance localName
        bundle pkg →
      Cont compl zero endpoint →
        Cont endpoint one booleanSource →
          Cont booleanSource localName stoneRead →
            PkgSig bundle provenance pkg →
              PkgSig bundle stoneRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row stoneRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
                        hsame row one ∨ hsame row order ∨ hsame row endpoint ∨
                          hsame row booleanSource ∨ hsame row stoneRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont compl zero endpoint ∧
                        Cont endpoint one booleanSource ∧
                          Cont booleanSource localName stoneRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle stoneRead pkg)
                    hsame ∧
                  UnaryHistory endpoint ∧ UnaryHistory booleanSource ∧
                    UnaryHistory stoneRead := by
  -- BEDC touchpoint anchor: BooleanAlgebraCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows complZero endpointOne booleanSourceLocalName provenancePkg stonePkg
  obtain ⟨_joinUnary, _meetUnary, complUnary, zeroUnary, oneUnary, _orderUnary,
    _transportUnary, _replayUnary, _provenanceUnary, localNameUnary, _joinMeetOrder,
    _complZeroReplay, _transportReplayProvenance, _carrierProvenancePkg,
    _carrierLocalNamePkg⟩ := carrierRows
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed complUnary zeroUnary complZero
  have booleanSourceUnary : UnaryHistory booleanSource :=
    unary_cont_closed endpointUnary oneUnary endpointOne
  have stoneReadUnary : UnaryHistory stoneRead :=
    unary_cont_closed booleanSourceUnary localNameUnary booleanSourceLocalName
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row stoneRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
              hsame row one ∨ hsame row order ∨ hsame row endpoint ∨
                hsame row booleanSource ∨ hsame row stoneRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont compl zero endpoint ∧ Cont endpoint one booleanSource ∧
              Cont booleanSource localName stoneRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle stoneRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro stoneRead ⟨hsame_refl stoneRead, stoneReadUnary⟩
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
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, complZero, endpointOne, booleanSourceLocalName, provenancePkg,
          stonePkg⟩
  }
  exact ⟨cert, endpointUnary, booleanSourceUnary, stoneReadUnary⟩

theorem BooleanAlgebraStoneSourceLatticeForwardConsumer [AskSetup] [PackageSetup]
    {join meet compl zero one order transport replay provenance localName endpoint booleanSource
      stoneRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BooleanAlgebraCarrier join meet compl zero one order transport replay provenance localName
        bundle pkg →
      Cont compl zero endpoint →
        Cont endpoint one booleanSource →
          Cont booleanSource localName stoneRead →
            Cont order localName stoneRead →
              PkgSig bundle provenance pkg →
                PkgSig bundle stoneRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row stoneRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
                          hsame row one ∨ hsame row order ∨ hsame row endpoint ∨
                            hsame row booleanSource ∨ hsame row stoneRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont compl zero endpoint ∧
                          Cont endpoint one booleanSource ∧
                            Cont booleanSource localName stoneRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle stoneRead pkg)
                      hsame ∧
                    SemanticNameCert
                        (fun row : BHist => hsame row stoneRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row join ∨ hsame row meet ∨ hsame row compl ∨
                            hsame row zero ∨ hsame row one ∨ hsame row order ∨
                              hsame row stoneRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont order localName stoneRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle stoneRead pkg)
                        hsame ∧
                      UnaryHistory endpoint ∧ UnaryHistory booleanSource ∧
                        UnaryHistory stoneRead := by
  intro carrierRows complZero endpointOne booleanSourceLocalName orderLocalName
    provenancePkg stonePkg
  have sourceDet :=
    BooleanAlgebraCarrier_stone_source_lattice_determinacy
      (join := join) (meet := meet) (compl := compl) (zero := zero) (one := one)
      (order := order) (transport := transport) (replay := replay)
      (provenance := provenance) (localName := localName) (endpoint := endpoint)
      (booleanSource := booleanSource) (stoneRead := stoneRead) (bundle := bundle) (pkg := pkg)
      carrierRows complZero endpointOne booleanSourceLocalName provenancePkg stonePkg
  have forward :=
    BooleanAlgebraCarrier_stone_duality_forward_route
      (join := join) (meet := meet) (compl := compl) (zero := zero) (one := one)
      (order := order) (transport := transport) (replay := replay)
      (provenance := provenance) (localName := localName) (stoneRead := stoneRead)
      (bundle := bundle) (pkg := pkg) carrierRows orderLocalName provenancePkg stonePkg
  exact
    ⟨sourceDet.left, forward.left, sourceDet.right.left, sourceDet.right.right.left,
      sourceDet.right.right.right⟩

theorem BooleanAlgebraStoneHandoffForwardConsumer [AskSetup] [PackageSetup]
    {join meet compl zero one order transport replay provenance localName stoneRead
      handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BooleanAlgebraCarrier join meet compl zero one order transport replay provenance localName
        bundle pkg →
      Cont order localName stoneRead →
        Cont stoneRead provenance handoffRead →
          PkgSig bundle provenance pkg →
            PkgSig bundle stoneRead pkg →
              PkgSig bundle handoffRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
                        hsame row one ∨ hsame row order ∨ hsame row stoneRead ∨
                          hsame row handoffRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont order localName stoneRead ∧
                        Cont stoneRead provenance handoffRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle handoffRead pkg)
                    hsame ∧
                  SemanticNameCert
                      (fun row : BHist => hsame row stoneRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row join ∨ hsame row meet ∨ hsame row compl ∨ hsame row zero ∨
                          hsame row one ∨ hsame row order ∨ hsame row stoneRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont order localName stoneRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle stoneRead pkg)
                      hsame ∧
                    UnaryHistory stoneRead ∧ UnaryHistory handoffRead := by
  intro carrierRows stoneRoute handoffRoute provenancePkg stonePkg handoffPkg
  have handoff :=
    BooleanAlgebraCarrier_stone_duality_handoff
      (join := join) (meet := meet) (compl := compl) (zero := zero) (one := one)
      (order := order) (transport := transport) (replay := replay)
      (provenance := provenance) (localName := localName) (stoneRead := stoneRead)
      (handoffRead := handoffRead) (bundle := bundle) (pkg := pkg) carrierRows
      stoneRoute handoffRoute provenancePkg handoffPkg
  have forward :=
    BooleanAlgebraCarrier_stone_duality_forward_route
      (join := join) (meet := meet) (compl := compl) (zero := zero) (one := one)
      (order := order) (transport := transport) (replay := replay)
      (provenance := provenance) (localName := localName) (stoneRead := stoneRead)
      (bundle := bundle) (pkg := pkg) carrierRows stoneRoute provenancePkg stonePkg
  exact ⟨handoff.left, forward.left, handoff.right.left, handoff.right.right⟩

end BEDC.Derived.BooleanalgebraUp
