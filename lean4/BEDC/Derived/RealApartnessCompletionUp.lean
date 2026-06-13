import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealApartnessCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealApartnessCompletionCarrier [AskSetup] [PackageSetup]
    (apartness separation completion stream readback tolerance sealRow transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: RealApartnessCompletionUp BHist ProbeBundle Pkg PkgSig UnaryHistory Cont
  UnaryHistory apartness ∧ UnaryHistory separation ∧ UnaryHistory completion ∧
    UnaryHistory stream ∧ UnaryHistory readback ∧ UnaryHistory tolerance ∧
      UnaryHistory sealRow ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont apartness separation completion ∧ Cont stream readback tolerance ∧
            Cont tolerance sealRow replay ∧ Cont transport replay provenance ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem RealApartnessCompletionObligationSurface [AskSetup] [PackageSetup]
    {apartness separation completion stream readback tolerance sealRow transport replay
      provenance localName separatedRead readbackRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealApartnessCompletionCarrier apartness separation completion stream readback tolerance
        sealRow transport replay provenance localName bundle pkg →
      Cont apartness separation separatedRead →
        Cont separatedRead completion readbackRead →
          Cont readbackRead tolerance sealedRead →
            PkgSig bundle sealedRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row apartness ∨ hsame row separation ∨ hsame row completion ∨
                      hsame row stream ∨ hsame row readback ∨ hsame row tolerance ∨
                        hsame row separatedRead ∨ hsame row readbackRead ∨
                          hsame row sealedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont apartness separation separatedRead ∧
                      Cont separatedRead completion readbackRead ∧
                        Cont readbackRead tolerance sealedRead ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle sealedRead pkg)
                  hsame ∧
                UnaryHistory separatedRead ∧ UnaryHistory readbackRead ∧
                  UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: RealApartnessCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier separatedRoute readbackRoute sealedRoute sealedPkg
  obtain ⟨apartnessUnary, separationUnary, completionUnary, _streamUnary, _readbackUnary,
    toleranceUnary, _sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _apartnessSeparationCompletion, _streamReadbackTolerance,
    _toleranceSealReplay, _transportReplayProvenance, provenancePkg, _localNamePkg⟩ := carrier
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed apartnessUnary separationUnary separatedRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed separatedUnary completionUnary readbackRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed readbackReadUnary toleranceUnary sealedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row apartness ∨ hsame row separation ∨ hsame row completion ∨
              hsame row stream ∨ hsame row readback ∨ hsame row tolerance ∨
                hsame row separatedRead ∨ hsame row readbackRead ∨ hsame row sealedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont apartness separation separatedRead ∧
              Cont separatedRead completion readbackRead ∧
                Cont readbackRead tolerance sealedRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle sealedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealedRead ⟨hsame_refl sealedRead, sealedUnary⟩
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
      exact ⟨source.right, separatedRoute, readbackRoute, sealedRoute, provenancePkg, sealedPkg⟩
  }
  exact ⟨cert, separatedUnary, readbackReadUnary, sealedUnary⟩

theorem RealApartnessCompletionLocatedTailObligation [AskSetup] [PackageSetup]
    {apartness separation completion stream readback tolerance sealRow transport replay
      provenance localName tailRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealApartnessCompletionCarrier apartness separation completion stream readback tolerance
        sealRow transport replay provenance localName bundle pkg →
      Cont completion stream tailRead →
        Cont tailRead tolerance sealRead →
          PkgSig bundle sealRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row apartness ∨ hsame row separation ∨ hsame row completion ∨
                    hsame row stream ∨ hsame row readback ∨ hsame row tolerance ∨
                      hsame row tailRead ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont completion stream tailRead ∧
                    Cont tailRead tolerance sealRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle sealRead pkg)
                hsame ∧
              UnaryHistory tailRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: RealApartnessCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier tailRoute sealRoute sealPkg
  obtain ⟨_apartnessUnary, _separationUnary, completionUnary, streamUnary, _readbackUnary,
    toleranceUnary, _sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _apartnessSeparationCompletion, _streamReadbackTolerance,
    _toleranceSealReplay, _transportReplayProvenance, provenancePkg, _localNamePkg⟩ :=
      carrier
  have tailUnary : UnaryHistory tailRead :=
    unary_cont_closed completionUnary streamUnary tailRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary toleranceUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row apartness ∨ hsame row separation ∨ hsame row completion ∨
              hsame row stream ∨ hsame row readback ∨ hsame row tolerance ∨
                hsame row tailRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont completion stream tailRead ∧
              Cont tailRead tolerance sealRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
                      source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, tailRoute, sealRoute, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, tailUnary, sealReadUnary⟩

theorem RealApartnessCompletionRegularReadbackDiscipline [AskSetup] [PackageSetup]
    {apartness separation completion stream readback tolerance sealRow transport replay
      provenance localName windowRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealApartnessCompletionCarrier apartness separation completion stream readback tolerance
        sealRow transport replay provenance localName bundle pkg →
      Cont stream readback windowRead →
        Cont windowRead tolerance regularRead →
          Cont regularRead sealRow sealRead →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row stream ∨ hsame row readback ∨ hsame row tolerance ∨
                      hsame row windowRead ∨ hsame row regularRead ∨ hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont stream readback windowRead ∧
                      Cont windowRead tolerance regularRead ∧
                        Cont regularRead sealRow sealRead ∧ PkgSig bundle provenance pkg ∧
                          PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory windowRead ∧ UnaryHistory regularRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: RealApartnessCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier windowRoute regularRoute sealRoute sealPkg
  obtain ⟨_apartnessUnary, _separationUnary, _completionUnary, streamUnary, readbackUnary,
    toleranceUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _apartnessSeparationCompletion, _streamReadbackTolerance,
    _toleranceSealReplay, _transportReplayProvenance, provenancePkg, _localNamePkg⟩ :=
      carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed streamUnary readbackUnary windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary toleranceUnary regularRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary sealUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row stream ∨ hsame row readback ∨ hsame row tolerance ∨
              hsame row windowRead ∨ hsame row regularRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont stream readback windowRead ∧
              Cont windowRead tolerance regularRead ∧
                Cont regularRead sealRow sealRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, windowRoute, regularRoute, sealRoute, provenancePkg, sealPkg⟩
  }
  exact ⟨cert, windowUnary, regularUnary, sealReadUnary⟩

theorem RealApartnessCompletionFiniteApartnessCompletionObligation [AskSetup] [PackageSetup]
    {apartness separation completion stream readback tolerance sealRow transport replay
      provenance localName separatedRead completionRead windowRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealApartnessCompletionCarrier apartness separation completion stream readback tolerance
        sealRow transport replay provenance localName bundle pkg →
      Cont apartness separation separatedRead →
        Cont separatedRead completion completionRead →
          Cont stream readback windowRead →
            Cont windowRead tolerance regularRead →
              Cont completionRead regularRead sealRead →
                PkgSig bundle sealRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row apartness ∨ hsame row separation ∨ hsame row completion ∨
                          hsame row stream ∨ hsame row readback ∨ hsame row tolerance ∨
                            hsame row separatedRead ∨ hsame row completionRead ∨
                              hsame row windowRead ∨ hsame row regularRead ∨
                                hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont apartness separation separatedRead ∧
                          Cont separatedRead completion completionRead ∧
                            Cont stream readback windowRead ∧
                              Cont windowRead tolerance regularRead ∧
                                Cont completionRead regularRead sealRead ∧
                                  PkgSig bundle sealRead pkg)
                      hsame ∧
                    UnaryHistory completionRead ∧ UnaryHistory regularRead ∧
                      UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: RealApartnessCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier separatedRoute completionRoute windowRoute regularRoute sealRoute sealPkg
  obtain ⟨apartnessUnary, separationUnary, completionUnary, streamUnary, readbackUnary,
    toleranceUnary, _sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _apartnessSeparationCompletion, _streamReadbackTolerance,
    _toleranceSealReplay, _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ :=
      carrier
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed apartnessUnary separationUnary separatedRoute
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed separatedUnary completionUnary completionRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed streamUnary readbackUnary windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary toleranceUnary regularRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed completionReadUnary regularUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row apartness ∨ hsame row separation ∨ hsame row completion ∨
              hsame row stream ∨ hsame row readback ∨ hsame row tolerance ∨
                hsame row separatedRead ∨ hsame row completionRead ∨
                  hsame row windowRead ∨ hsame row regularRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont apartness separation separatedRead ∧
              Cont separatedRead completion completionRead ∧
                Cont stream readback windowRead ∧
                  Cont windowRead tolerance regularRead ∧
                    Cont completionRead regularRead sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, separatedRoute, completionRoute, windowRoute, regularRoute, sealRoute,
          sealPkg⟩
  }
  exact ⟨cert, completionReadUnary, regularUnary, sealReadUnary⟩

theorem RealApartnessCompletionLedgerExhaustion [AskSetup] [PackageSetup]
    {apartness separation completion stream readback tolerance sealRow transport replay
      provenance localName ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealApartnessCompletionCarrier apartness separation completion stream readback tolerance
        sealRow transport replay provenance localName bundle pkg →
      Cont sealRow replay ledgerRead →
        PkgSig bundle ledgerRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row apartness ∨ hsame row separation ∨ hsame row completion ∨
                  hsame row stream ∨ hsame row readback ∨ hsame row tolerance ∨
                    hsame row sealRow ∨ hsame row transport ∨ hsame row replay ∨
                      hsame row provenance ∨ hsame row localName ∨ hsame row ledgerRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont sealRow replay ledgerRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg)
              hsame ∧
            UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: RealApartnessCompletionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier ledgerRoute ledgerPkg
  obtain ⟨_apartnessUnary, _separationUnary, _completionUnary, _streamUnary,
    _readbackUnary, _toleranceUnary, sealUnary, _transportUnary, replayUnary,
    _provenanceUnary, _localNameUnary, _apartnessSeparationCompletion,
    _streamReadbackTolerance, _toleranceSealReplay, _transportReplayProvenance,
    provenancePkg, _localNamePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed sealUnary replayUnary ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row apartness ∨ hsame row separation ∨ hsame row completion ∨
              hsame row stream ∨ hsame row readback ∨ hsame row tolerance ∨
                hsame row sealRow ∨ hsame row transport ∨ hsame row replay ∨
                  hsame row provenance ∨ hsame row localName ∨ hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont sealRow replay ledgerRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
      exact ⟨source.right, ledgerRoute, provenancePkg, ledgerPkg⟩
  }
  exact ⟨cert, ledgerUnary⟩

theorem RealApartnessCompletionWindowDeterminacy [AskSetup] [PackageSetup]
    {apartness separation completion stream readback tolerance sealRow transport replay
      provenance localName windowRead regularRead sealRead windowRead' regularRead'
      sealRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealApartnessCompletionCarrier apartness separation completion stream readback tolerance
        sealRow transport replay provenance localName bundle pkg →
      Cont stream readback windowRead →
        Cont windowRead tolerance regularRead →
          Cont regularRead sealRow sealRead →
            Cont stream readback windowRead' →
              Cont windowRead' tolerance regularRead' →
                Cont regularRead' sealRow sealRead' →
                  hsame windowRead windowRead' ∧ hsame regularRead regularRead' ∧
                    hsame sealRead sealRead' ∧ UnaryHistory windowRead ∧
                      UnaryHistory regularRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: RealApartnessCompletionCarrier BHist Cont hsame UnaryHistory
  intro carrier windowRoute regularRoute sealRoute windowRoute' regularRoute' sealRoute'
  obtain ⟨_apartnessUnary, _separationUnary, _completionUnary, streamUnary, readbackUnary,
    toleranceUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _apartnessSeparationCompletion, _streamReadbackTolerance,
    _toleranceSealReplay, _transportReplayProvenance, _provenancePkg, _localNamePkg⟩ :=
      carrier
  have sameWindow : hsame windowRead windowRead' :=
    cont_respects_hsame (hsame_refl stream) (hsame_refl readback) windowRoute windowRoute'
  have sameRegular : hsame regularRead regularRead' :=
    cont_respects_hsame sameWindow (hsame_refl tolerance) regularRoute regularRoute'
  have sameSeal : hsame sealRead sealRead' :=
    cont_respects_hsame sameRegular (hsame_refl sealRow) sealRoute sealRoute'
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed streamUnary readbackUnary windowRoute
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary toleranceUnary regularRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regularUnary sealUnary sealRoute
  exact
    ⟨sameWindow, sameRegular, sameSeal, windowUnary, regularUnary, sealReadUnary⟩

end BEDC.Derived.RealApartnessCompletionUp
