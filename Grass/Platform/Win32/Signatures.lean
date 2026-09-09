import Grass.ABI.Win64.Convention

/-!
# Physical parameter order for the selected console APIs

The parameter lists follow the Syntax sections of Microsoft's GetStdHandle,
WriteFile and ExitProcess documentation, retrieved 2026-09-09:
https://learn.microsoft.com/en-us/windows/console/getstdhandle
https://learn.microsoft.com/en-us/windows/win32/api/fileapi/nf-fileapi-writefile
https://learn.microsoft.com/en-us/windows/win32/api/processthreadsapi/nf-processthreadsapi-exitprocess

Source names are Grass aliases. `argumentCount` and `argumentIndex?` compute
their results from `parameters`; they are not separately maintained ABI inputs.
These signatures do not specify effects, permitted outcomes, or call safety.
-/
namespace Grass.Platform.Win32.Signatures

inductive Api where
  | getStdHandle | writeFile | exitProcess
deriving Repr, DecidableEq

inductive ParameterKind where
  | handle | pointer | uint32
deriving Repr, DecidableEq

structure Parameter where
  sourceName : String
  nativeName : String
  kind : ParameterKind
deriving Repr, DecidableEq

def apiName : Api → String
  | .getStdHandle => "GetStdHandle"
  | .writeFile => "WriteFile"
  | .exitProcess => "ExitProcess"

def apis : List Api := [.getStdHandle, .writeFile, .exitProcess]

def resolveName? (name : String) : Option Api :=
  apis.find? fun api => apiName api == name

def importName (api : Api) : String := "__imp_" ++ apiName api

def resolveImport? (name : String) : Option Api :=
  apis.find? fun api => importName api == name

def parameters : Api → List Parameter
  | .getStdHandle => [⟨"stdHandle", "nStdHandle", .uint32⟩]
  | .writeFile =>
    [⟨"file", "hFile", .handle⟩,
     ⟨"buffer", "lpBuffer", .pointer⟩,
     ⟨"bytesToWrite", "nNumberOfBytesToWrite", .uint32⟩,
     ⟨"bytesWritten", "lpNumberOfBytesWritten", .pointer⟩,
     ⟨"overlapped", "lpOverlapped", .pointer⟩]
  | .exitProcess => [⟨"exitCode", "uExitCode", .uint32⟩]

def argumentCount (api : Api) : Nat := (parameters api).length

def argumentIndex? (api : Api) (field : String) : Option Nat :=
  (parameters api).findIdx? fun parameter => parameter.sourceName == field

theorem resolveName?_exact {name : String} {api : Api}
    (success : resolveName? name = some api) : apiName api = name := by
  have h := List.find?_some success
  simpa using h

theorem resolveImport?_exact {name : String} {api : Api}
    (success : resolveImport? name = some api) : importName api = name := by
  have h := List.find?_some success
  simpa using h

theorem argumentIndex?_exact {api : Api} {field : String} {index : Nat}
    (success : argumentIndex? api field = some index) :
    ∃ bounded : index < (parameters api).length,
      (parameters api)[index].sourceName = field := by
  obtain ⟨bounded, found, _⟩ := List.findIdx?_eq_some_iff_getElem.mp success
  exact ⟨bounded, by simpa using found⟩

theorem argumentIndex?_bounded {api : Api} {field : String} {index : Nat}
    (success : argumentIndex? api field = some index) : index < argumentCount api :=
  (argumentIndex?_exact success).1

theorem parameter_names_unique (api : Api) :
    ((parameters api).map Parameter.sourceName).Nodup := by
  cases api <;> decide

end Grass.Platform.Win32.Signatures
