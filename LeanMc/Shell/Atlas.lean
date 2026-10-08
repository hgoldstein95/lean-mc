/-!
# Block texture atlas

The atlas is generated rather than loaded: a `256 × 256` RGBA image of
`16 × 16` tiles, each drawn from a small deterministic noise function. Tile
numbers match `Block.tile`. This is cosmetic and unverified.
-/

namespace LeanMc.Shell.Atlas

/-- Atlas width and height in pixels. -/
def size : Nat := 256

/-- A cheap integer hash for texture noise. -/
def hash (x y salt : Nat) : Nat :=
  let h := (x * 374761393 + y * 668265263 + salt * 2246822519) % 4294967296
  let h := ((h ^^^ (h >>> 13)) * 1274126177) % 4294967296
  h ^^^ (h >>> 16)

/-- Noise in `[-amp, amp]`. -/
def jitter (x y salt amp : Nat) : Int :=
  (hash x y salt % (2 * amp + 1) : Nat) - (amp : Int)

def clamp (v : Int) : UInt8 :=
  (max 0 (min 255 v)).toNat.toUInt8

/-- A colour brightened or darkened by `d`. -/
def rgb (r g b : Nat) (d : Int := 0) : UInt8 × UInt8 × UInt8 :=
  (clamp (r + d), clamp (g + d), clamp (b + d))

/-- Colour of pixel `(x, y)` of a tile, with `y = 0` at the top. -/
def tilePixel (tile x y : Nat) : UInt8 × UInt8 × UInt8 :=
  let dirt := rgb 134 96 67 (jitter x y 2 12)
  let grass := rgb 96 160 54 (jitter x y 3 14)
  match tile with
  | 0 => rgb 72 72 72 (jitter x y 0 36)                      -- bedrock
  | 1 => rgb 128 128 128 (jitter x y 1 10)                   -- stone
  | 2 => dirt
  | 3 => grass                                               -- grass top
  | 4 => if y < 3 + hash x 0 4 % 3 then grass else dirt      -- grass side
  | 5 => rgb 219 207 163 (jitter x y 5 8)                    -- sand
  | 6 => rgb 103 82 50 (jitter x 0 6 14 + jitter x y 6 4)    -- log side
  | 7 =>                                                     -- log top
    let dx := ((2 * x : Nat) : Int) - 15
    let dy := ((2 * y : Nat) : Int) - 15
    let ring := max dx.natAbs dy.natAbs / 4
    if ring % 2 == 0 then rgb 172 138 86 (jitter x y 7 5) else rgb 128 100 58 (jitter x y 7 5)
  | 8 =>                                                     -- leaves
    if hash x y 8 % 5 == 0 then rgb 30 70 22 else rgb 58 122 40 (jitter x y 8 16)
  | 9 =>                                                     -- planks
    if y % 4 == 3 then rgb 112 88 52 else rgb 166 134 82 (jitter x y 9 5 + jitter 0 (y / 4) 9 8)
  | 10 =>                                                    -- cobble
    let sx := x + (y / 4 % 2) * 2
    if sx % 4 == 0 || y % 4 == 0 then rgb 78 78 78 (jitter x y 10 6)
    else rgb 126 126 126 (jitter (sx / 4) (y / 4) 10 22 + jitter x y 11 5)
  | _ => (255, 0, 255)

/-- The whole atlas as RGBA8, row by row from the top. -/
def pixels : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (size * size * 4)
  for py in [0:size] do
    for px in [0:size] do
      let (r, g, b) := tilePixel (py / 16 * 16 + px / 16) (px % 16) (py % 16)
      out := out.push r |>.push g |>.push b |>.push 255
  return out

end LeanMc.Shell.Atlas
