{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Main (main) where

import Codec.Picture
import Control.Applicative
import Control.Lens hiding ((<.>))
import Control.Monad
import Control.Monad.Action
import Control.Monad.Action.Left qualified as L
import Control.Monad.State
import Data.Char
import Data.Maybe
import Data.Ord
import Data.Vector.Storable qualified as V
import Linear.Affine
import Linear.Epsilon
import Linear.Metric
import Linear.Quaternion
import Linear.V3
import Linear.V4
import Linear.Vector hiding (lerp)
import Options.Applicative qualified as O
import System.FilePath
import Text.Read (readMaybe)

sampleBilinear ::
  forall b px.
  ( Floating b,
    RealFrac b,
    Pixel px,
    Integral (PixelBaseComponent px)
  ) =>
  Image px -> b -> b -> px
sampleBilinear img@Image {imageHeight, imageWidth} x y =
  let x' = fromIntegral imageHeight * (x / pi + 1 / 2)
      y' = fromIntegral imageWidth * y / (2 * pi)
      x1 = clamp (0, imageHeight - 1) $ floor x'
      x2 = clamp (0, imageHeight - 1) $ ceiling x'
      y1 = floor y' `mod` imageWidth
      y2 = ceiling y' `mod` imageWidth
      lerp t _ a b = floor $ (1 - t) * fromIntegral a + t * fromIntegral b
      xFrac = x' - fromIntegral @Int (floor x')
      yFrac = y' - fromIntegral @Int (floor y')
   in mixWith
        (lerp xFrac)
        (mixWith (lerp yFrac) (pixelAt img y1 x1) (pixelAt img y2 x1))
        (mixWith (lerp yFrac) (pixelAt img y1 x2) (pixelAt img y2 x2))

outerProductWith :: (Functor f, Functor g) => (a -> b -> c) -> f a -> g b -> f (g c)
outerProductWith f xs ys = fmap (flip fmap ys . f) xs

sampleBicubic ::
  forall b px.
  ( Floating b,
    RealFrac b,
    Pixel px,
    Integral (PixelBaseComponent px),
    Bounded (PixelBaseComponent px)
  ) =>
  Image px -> b -> b -> px
sampleBicubic img@Image {imageHeight, imageWidth, imageData} x y =
  let x' = fromIntegral imageHeight * (x / pi + 1 / 2)
      y' = fromIntegral imageWidth * y / (2 * pi)
      xInt = floor x' :: Int
      yInt = floor y' :: Int
      xFrac = x' - fromIntegral xInt
      yFrac = y' - fromIntegral yInt
      !xs = clamp (0, imageHeight - 1) . (+ xInt) <$> V4 (-1) 0 1 2
      !ys = (`mod` imageWidth) . (+ yInt) <$> V4 (-1) 0 1 2
      compAt :: Int -> Int -> Int -> PixelBaseComponent px
      compAt xCoord yCoord ci =
        imageData V.! (pixelBaseIndex img xCoord yCoord + ci)
      catmullRom :: (Floating t) => t -> t -> t -> t -> t -> t
      catmullRom t p0 p1 p2 p3 =
        0.5
          * ( (2 * p1)
                + (-p0 + p2) * t
                + (2 * p0 - 5 * p1 + 4 * p2 - p3) * t * t
                + (-p0 + 3 * p1 - 3 * p2 + p3) * t * t * t
            )
      sampleComponent :: Int -> PixelBaseComponent px
      sampleComponent i =
        let ps = outerProductWith (\a b -> fromIntegral @_ @b $ compAt b a i) xs ys
            V4 r0 r1 r2 r3 = (\p -> catmullRom yFrac (p ^. _x) (p ^. _y) (p ^. _z) (p ^. _w)) <$> ps
            lo = fromIntegral @(PixelBaseComponent px) minBound
            hi = fromIntegral @(PixelBaseComponent px) maxBound
         in round . clamp (lo, hi) $
              catmullRom xFrac r0 r1 r2 r3
      template = pixelAt img 0 0
   in mixWith (const . const . sampleComponent) template template

type ProjectionMode = (V3 Double -> V3 Double -> V3 Double -> Double -> Double -> (Double, Double))

projectCubeSphere ::
  ( Pixel px,
    Integral (PixelBaseComponent px),
    Bounded (PixelBaseComponent px)
  ) =>
  ProjectionMode -> Int -> Int -> V3 Double -> V3 Double -> V3 Double -> Image px -> Image px
projectCubeSphere f xres yres c00 c01 c10 img =
  generateImage
    ( \a b ->
        let a' = fromIntegral a / fromIntegral xres
            b' = fromIntegral b / fromIntegral yres
            (phi, theta) = f c00 c01 c10 a' b'
         in sampleBicubic img phi theta
    )
    xres
    yres

gnomonic :: ProjectionMode
gnomonic c00 c01 c10 a b =
  let v0 = c01 .-. c00
      v1 = c10 .-. c00
      V3 x y z = normalize $ c00 .+^ a *^ v0 .+^ b *^ v1
      phi = asin z
      theta = atan2 x y
   in (phi, theta)

-- Roşca–Plonka area-preserving map T : (-beta,beta)^2 -> R^2, where beta = sqrt(pi/6)
tMap :: Double -> Double -> (Double, Double)
tMap x y
  | nearZero x && nearZero y = (0, 0)
  | abs y <= abs x =
      let a = (y * pi) / (12 * x)
          denom = sqrt (sqrt 2 - cos a)
          s = (sqrt (sqrt 2) * x) / sqrt (pi / 6)
          x1 = s * ((sqrt 2 * cos a) - 1) / denom
          y1 = s * (sqrt 2 * sin a) / denom
       in (x1, y1)
  | otherwise =
      let a = (x * pi) / (12 * y)
          denom = sqrt $ sqrt 2 - cos a
          s = (sqrt (sqrt 2) * y) / sqrt (pi / 6)
          x1 = s * (sqrt 2 * sin a) / denom
          y1 = s * ((sqrt 2 * cos a) - 1) / denom
       in (x1, y1)

invLambert :: Double -> Double -> V3 Double
invLambert x y =
  let r2 = x * x + y * y
      k = sqrt $ 1 - r2 / 4
   in V3 (x * k) (y * k) (1 - r2 / 2)

roscaPlonka :: ProjectionMode
roscaPlonka c00 c01 c10 a b =
  let v0 = c01 .-. c00
      v1 = c10 .-. c00

      e0 = normalize v0
      n = normalize $ v1 `cross` e0
      e1 = normalize $ n `cross` e0

      toGlobal (V3 lx ly lz) = (lx *^ e0) .+^ (ly *^ e1) .+^ (lz *^ n)

      x = (2 * a - 1) * sqrt (pi / 6)
      y = (2 * b - 1) * sqrt (pi / 6)
      (xL, yL) = tMap x y
      V3 gx gy gz = normalize . toGlobal $ invLambert xL yL
      phi = asin gz
      theta = atan2 gx gy
   in (-phi, theta)

dynamicPixelMapI ::
  ( forall px.
    (Pixel px, Integral (PixelBaseComponent px), Bounded (PixelBaseComponent px)) =>
    Image px -> Image px
  ) ->
  DynamicImage ->
  Either String DynamicImage
dynamicPixelMapI f = aux
  where
    aux (ImageY8 i) = Right $ ImageY8 (f i)
    aux (ImageY16 i) = Right $ ImageY16 (f i)
    aux (ImageY32 i) = Right $ ImageY32 (f i)
    aux (ImageYF _) = Left "non-integral pixel base component"
    aux (ImageYA8 i) = Right $ ImageYA8 (f i)
    aux (ImageYA16 i) = Right $ ImageYA16 (f i)
    aux (ImageRGB8 i) = Right $ ImageRGB8 (f i)
    aux (ImageRGB16 i) = Right $ ImageRGB16 (f i)
    aux (ImageRGBF _) = Left "non-integral pixel base component"
    aux (ImageRGBA8 i) = Right $ ImageRGBA8 (f i)
    aux (ImageRGBA16 i) = Right $ ImageRGBA16 (f i)
    aux (ImageYCbCr8 i) = Right $ ImageYCbCr8 (f i)
    aux (ImageCMYK8 i) = Right $ ImageCMYK8 (f i)
    aux (ImageCMYK16 i) = Right $ ImageCMYK16 (f i)

-- genCube :: Double -> V3 Double -> [V3 Double]
-- genCube theta (normalize -> axis) =
--   let r = Quaternion (cos $ theta / 2) (sin (theta / 2) *^ axis)
--       vs = V3 <$> [-1, 1] <*> [-1, 1] <*> [-1, 1]
--    in (rotate r <$>) vs

genCube :: Quaternion Double -> [V3 Double]
genCube (normalize -> r) =
  let vs = V3 <$> [-1, 1] <*> [-1, 1] <*> [-1, 1]
   in (rotate r <$>) vs

data CubeComponent = Zero | X | One deriving (Show, Eq, Ord, Enum, Bounded)

complement :: CubeComponent -> CubeComponent
complement = \case
  Zero -> One
  X -> X
  One -> Zero

dimension :: (Foldable f, Functor f) => f CubeComponent -> Int
dimension = sum . fmap (\case X -> 1; _ -> 0)

vertexToIntegral :: (Foldable f, Functor f) => f CubeComponent -> Int
vertexToIntegral = foldl ((+) . (* 2)) 0 . fmap \case Zero -> 0; One -> 1; X -> error "Undefined component"

cubeFaces :: [V3 CubeComponent]
cubeFaces = filter ((== 2) . dimension) $ V3 <$> [minBound .. maxBound] <*> [minBound .. maxBound] <*> [minBound .. maxBound]

mapTriple :: (a -> b) -> (a, a, a) -> (b, b, b)
mapTriple f (x, y, z) = (f x, f y, f z)

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (x, y, z) = f x y z

faceToVertices :: V3 CubeComponent -> (Int, Int, Int)
faceToVertices (V3 a X X) = mapTriple vertexToIntegral (V3 a Zero Zero, V3 a (complement a) a, V3 a a (complement a))
faceToVertices (V3 X a X) = mapTriple vertexToIntegral (V3 Zero a Zero, V3 a a (complement a), V3 (complement a) a a)
faceToVertices (V3 X X a) = mapTriple vertexToIntegral (V3 Zero Zero a, V3 (complement a) a a, V3 a (complement a) a)
faceToVertices _ = error "Not a face"

cubeComponentsToString :: (Foldable f, Functor f) => f CubeComponent -> String
cubeComponentsToString = foldr (:) "" . fmap \case Zero -> '0'; X -> 'X'; One -> '1'

newtype Parser a = Parser {getParser :: StateT String Maybe a}
  deriving (Functor, Applicative, Alternative, Monad, MonadState String)

runParser :: Parser a -> String -> Maybe a
runParser = evalStateT . getParser

instance (Monad m, LeftModule m (StateT String Maybe)) => LeftModule m Parser where
  ljoin = Parser . ljoin . fmap getParser

instance (Monad m, RightModule m (StateT String Maybe)) => RightModule m Parser where
  rjoin = Parser . rjoin . getParser

instance (Functor f, LeftModule (StateT String Maybe) f) => LeftModule Parser f where
  ljoin = ljoin . getParser

instance (Functor f, RightModule (StateT String Maybe) f) => RightModule Parser f where
  rjoin = rjoin . fmap getParser

predP :: (Char -> Bool) -> Parser Char
predP p = L.do
  s <- get @_ @Parser
  (c', s') <- uncons s
  put @_ @Parser s'
  if p c' then pure c' else empty

charP :: Char -> Parser Char
charP = predP . (==)

stringP :: String -> Parser String
stringP = traverse charP

numP :: (Read a) => Parser a
numP = L.do
  sgn <- optional $ charP '-'
  intPart <- some (predP isDigit)
  fracPart <- optional $ (:) <$> charP '.' <*> many (predP isDigit)
  expPart <- optional $ (:) <$> predP ((== 'e') . toLower) <*> ((.:) <$> optional (charP '-') <*> many (predP isDigit))
  d <- readMaybe (sgn .: (intPart ++. fracPart ++. expPart))
  pure d

(.:) :: Maybe a -> [a] -> [a]
(.:) = flip . ap maybe $ flip (:)

infixl 5 ++.

(++.) :: [a] -> Maybe [a] -> [a]
(++.) = ap maybe (++)

chainl1 :: (Alternative f, Monad f) => f t -> f (t -> t -> t) -> f t
-- chainl1 p o = foldl (\a (f, y) -> f a y) <$> p <*> many ((,) <$> o <*> p)
chainl1 p o = p >>= rest
  where
    rest x =
      ( o >>= \f ->
          p >>= \y -> rest $ f x y
      )
        <|> pure x

chainr1 :: (Alternative f, Monad f) => f t -> f (t -> t -> t) -> f t
chainr1 p o =
  p
    >>= \x ->
      ( fmap ($ x) o
          <*> chainr1 p o
      )
        <|> pure x

addOpP :: (Num a) => Parser (a -> a -> a)
addOpP = charP '+' *> pure (+) <|> charP '-' *> pure (-)

multOpP :: (Fractional a) => Parser (a -> a -> a)
multOpP = charP '*' *> pure (*) <|> charP '/' *> pure (/)

funcOpP :: (Floating a) => Parser (a -> a)
funcOpP =
  stringP "exp" *> pure exp
    <|> stringP "log" *> pure log
    <|> stringP "sqrt" *> pure sqrt
    <|> stringP "sin" *> pure sin
    <|> stringP "cos" *> pure cos
    <|> stringP "tan" *> pure tan
    <|> stringP "asin" *> pure asin
    <|> stringP "acos" *> pure acos
    <|> stringP "atan" *> pure atan
    <|> stringP "sinh" *> pure sinh
    <|> stringP "cosh" *> pure cosh
    <|> stringP "tanh" *> pure tanh
    <|> stringP "asinh" *> pure asinh
    <|> stringP "acosh" *> pure acosh
    <|> stringP "atanh" *> pure atanh

constP :: (Floating a) => Parser a
constP =
  stringP "pi" *> pure pi
    <|> stringP "e" *> pure (exp 1)

hUnitP :: (Num a) => Parser (Quaternion a)
hUnitP =
  charP 'i' *> pure (Quaternion 0 $ V3 1 0 0)
    <|> charP 'j' *> pure (Quaternion 0 $ V3 0 1 0)
    <|> charP 'k' *> pure (Quaternion 0 $ V3 0 0 1)

skipSpaces :: Parser a -> Parser a
skipSpaces p = many (predP isSpace) *> p <* many (predP isSpace)

hImagP :: (Num a, RealFloat a, Read a) => Parser (Quaternion a)
hImagP = (*) <$> fmap (flip Quaternion zero) numP <*> skipSpaces hUnitP

hExprP :: (RealFloat a, Read a) => Parser (Quaternion a)
hExprP = chainl1 hSummandP addOpP

hSummandP :: (RealFloat a, Read a) => Parser (Quaternion a)
hSummandP = chainl1 hFactorP multOpP

hFactorP :: (RealFloat a, Read a) => Parser (Quaternion a)
hFactorP =
  skipSpaces $
    hUnitP
      <|> hImagP
      <|> fmap (flip Quaternion zero) numP
      <|> constP
      <|> funcOpP <*> hExprP
      <|> (charP '(' *> hExprP <* charP ')')

data GlobeOptions = GlobeOptions
  { globeFile :: FilePath,
    outputPath :: FilePath,
    mSize :: Maybe Int,
    mRotation :: Maybe (Quaternion Double)
  }

parseGlobeOptions :: O.ParserInfo GlobeOptions
parseGlobeOptions =
  let parser = do
        globeFile <- O.strOption (O.short 'g' <> O.long "globe" <> O.metavar "GLOBEFILE")
        outputPath <- O.strOption (O.short 'o' <> O.long "output" <> O.metavar "OUTPUTPATH")
        mSize <- fmap (>>= readMaybe) . O.optional $ O.strOption (O.short 's' <> O.long "size" <> O.metavar "SIZE")
        mRotation <- fmap (>>= runParser hExprP) . O.optional $ O.strOption (O.short 'r' <> O.long "rotation" <> O.metavar "ROTATION")
        pure GlobeOptions {..}
   in O.info (parser O.<**> O.helper) (O.fullDesc <> O.progDesc "Create a cube-shaped globe from GLOBEFILE")

main :: IO ()
main = do
  GlobeOptions {..} <- O.execParser parseGlobeOptions
  let size = fromMaybe 512 mSize
      rotation = fromMaybe 1 mRotation
      cube = genCube rotation
  print rotation
  Right globe <- readImage globeFile
  forM_ cubeFaces \face -> do
    let globeSample =
          either error id $
            dynamicPixelMapI (uncurry3 (projectCubeSphere roscaPlonka size size) . mapTriple (cube !!) $ faceToVertices face) globe
    saveTiffImage (outputPath ++ '_' : cubeComponentsToString face <.> "tiff") globeSample
