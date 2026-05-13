import Rule110CrossCheck.Parser
import Rule110CrossCheck.Registry
import Rule110CrossCheck.Reporting
import Rule110CrossCheck.Families.Mark
import Rule110CrossCheck.Families.Hist
import Rule110CrossCheck.Families.Ext
import Rule110CrossCheck.Families.Cont
import Rule110CrossCheck.Families.Sig
import Rule110CrossCheck.Families.Bundle
import Rule110CrossCheck.Families.Unary
import Rule110CrossCheck.Families.Ask
import Rule110CrossCheck.Families.ExternalBinary
import Rule110CrossCheck.Families.Gap
import Rule110CrossCheck.Families.Package
import Rule110CrossCheck.Families.NameCert
import Rule110CrossCheck.Families.Settled

namespace BEDC.Rule110CrossCheck

partial def hasDuplicateCase : List String -> Bool
  | [] => false
  | name :: rest => rest.contains name || hasDuplicateCase rest

def checkManifest (path : String) (manifest : Manifest) : Except String (List String) := do
  let family <- familyOfPath path
  if manifest.productions != 0 then
    throw s!"{family.name} manifest must have PRODUCTIONS 0, got {manifest.productions}"
  if manifest.assertions.length != manifest.assertionsDeclared then
    throw s!"assertion count mismatch: declared {manifest.assertionsDeclared}, parsed {manifest.assertions.length}"
  if hasDuplicateCase (manifest.assertions.map (·.name)) then
    throw "duplicate assertion case name"
  match family with
  | .markRefl => manifest.assertions.mapM (checkMarkRefl path)
  | .markSymm => manifest.assertions.mapM (checkMarkSymm path)
  | .markTrans => manifest.assertions.mapM (checkMarkTrans path)
  | .markNoConfusion => manifest.assertions.mapM (checkMarkNoConfusion path)
  | .histRefl => manifest.assertions.mapM (checkHistRefl path)
  | .histSymm => manifest.assertions.mapM (checkHistSymm path)
  | .histTrans => manifest.assertions.mapM (checkHistTrans path)
  | .histEmpty => manifest.assertions.mapM (checkHistEmpty path)
  | .histDistinct => manifest.assertions.mapM (checkHistDistinct path)
  | .ext => manifest.assertions.mapM (checkExtStep path)
  | .cont => manifest.assertions.mapM (checkContLike .cont "cont_holds" path)
  | .sigRel => manifest.assertions.mapM (checkSigRel path)
  | .sameSig => manifest.assertions.mapM (checkSameSig path)
  | .bundleLength => manifest.assertions.mapM (checkBundleLength path)
  | .bundleMembership => manifest.assertions.mapM (checkBundleMembership path)
  | .unary => manifest.assertions.mapM (checkUnary path)
  | .ask => manifest.assertions.mapM (checkAsk path)
  | .externalBinary => manifest.assertions.mapM (checkContLike .externalBinary "external_append_holds" path)
  | .gap => manifest.assertions.mapM (checkGap path)
  | .package => manifest.assertions.mapM (checkPackage path)
  | .nameCert => manifest.assertions.mapM (checkNameCert path)
  | .settled => manifest.assertions.mapM (checkSettled path)



def registeredManifests : List String :=
  registeredManifestSpecs.map (fun spec => "../" ++ spec.fst)

def usage : String :=
  "usage: cd rule110/lean-side && lake exe rule110-cross-check [manifest.enum.ct]..."

def formatFail (path : String) (e : CheckError) : String :=
  s!"FAIL kind={e.kind.name} path={path} case={e.caseName} message={e.message}"

def runOne (path : String) : IO UInt32 := do
  try
    let content <- IO.FS.readFile path
    match parseManifest content >>= checkManifest path with
    | Except.ok lines =>
        for line in lines do
          IO.println line
        pure 0
    | Except.error msg =>
        IO.eprintln (formatFail path {
          kind := FailKind.fixture,
          caseName := manifestCase,
          message := msg
        })
        pure 1
  catch e =>
    IO.eprintln (formatFail path {
      kind := FailKind.fixture,
      caseName := manifestCase,
      message := e.toString
    })
    pure 1

partial def runMany : List String -> IO UInt32
  | [] => pure 0
  | path :: rest => do
      let code <- runOne path
      let restCode <- runMany rest
      if code == 0 && restCode == 0 then pure 0 else pure 1

def run (args : List String) : IO UInt32 := do
  match args with
  | [] => runMany registeredManifests
  | _ => runMany args

end BEDC.Rule110CrossCheck

def main (args : List String) : IO UInt32 :=
  BEDC.Rule110CrossCheck.run args
