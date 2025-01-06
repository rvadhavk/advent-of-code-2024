module AoC2024 where

import System.IO.Unsafe
import Control.Monad (guard, forM, forM_)
import Control.Monad.State.Lazy
import Control.Monad.Trans.Maybe
import Control.Lens hiding ((<|), (|>), Empty, levels)
import Control.Lens.Fold
import Data.AdditiveGroup
import Data.Bits
import Data.Char (digitToInt, isDigit)
import Data.Foldable (toList)
import Data.Functor.Classes (eq1)
import Data.Graph (stronglyConnComp)
import qualified Data.IntMap as IM
import Data.Ix (inRange)
import Data.List hiding (filter)
import qualified Data.List.NonEmpty as NE
import Data.Map (Map, (!))
import qualified Data.Map as M
import Data.Maybe (fromMaybe, isJust)
import qualified Data.MultiMap as MM
import Data.Ord
import Data.Ratio
import qualified Data.Sequence as Seq
import Data.Sequence (Seq(..), (<|), (|>))
import qualified Data.Set as S
import Data.Set.Lens
import Data.Maybe (fromJust)
import Data.Void (Void)
import Debug.Trace
import Linear.V2
import Linear.V3
import Linear.Matrix hiding (transpose)
import Linear.Metric (dot, quadrance)
import qualified Linear.Matrix as LM
import Linear.Vector ((*^), zero)
import Prelude hiding (filter)
import Safe
import Text.Megaparsec 
  ( (<|>)
  , Parsec
  , anySingle
  , anySingleBut
  , atEnd
  , between
  , choice
  , eof
  , errorBundlePretty
  , many
  , notFollowedBy
  , oneOf
  , optional
  , parse
  , parseMaybe
  , parseTest
  , sepBy
  , sepBy1
  , sepEndBy
  , sepEndBy1
  , some
  , takeRest
  , try
  )
import Text.Megaparsec.Char (alphaNumChar, char, digitChar, letterChar, newline, hspace, space, string)
import Text.Megaparsec.Char.Lexer (decimal, signed)
import Witherable


-- Utilities for reading input and running solutions
data Mode = Real | Example

readInputForDay :: Int -> Mode -> IO String
readInputForDay n mode = readFile $ directory ++ show n where
  directory = case mode of
    Real -> "../input/"
    Example -> "../example_input/"


run :: Solution a -> Mode -> IO ()
run solution mode = do
  input <- readInputForDay (day solution) mode
  case mode of
    Example -> putStrLn $ "Input:\n" ++ input
    _ -> return ()
  putStrLn $ runSolution solution input

parseTestExample :: Show a => Solution a -> IO ()
parseTestExample Solution{day, parser} = do
  input <- readInputForDay day Example
  putStrLn $ "Input:\n" ++ input
  putStrLn $ "Output:"
  parseTest parser input

type Parser = Parsec Void String

data Solution a = Solution {
  day :: Int,
  parser :: Parser a,
  solver :: a -> [String]
}

runSolution :: Solution a -> String -> String
runSolution Solution{parser, solver} input = case parse parser "" input of
  Left err -> "Parse error:\n" ++ errorBundlePretty err
  Right parsedInput -> intercalate "\n" formattedAnswers  where
    headings = ["Part " ++ show i ++ ":\n" | i <- [(1 :: Int)..]]
    answers = solver parsedInput
    formattedAnswers = zipWith (++) headings answers

-- DAY 1

intPair :: Parser (Int, Int)
intPair = (,) <$> decimal <* hspace <*> decimal

day1 :: Solution [(Int, Int)]
day1 = Solution {
  day = 1,
  parser = sepEndBy intPair newline <* eof,
  solver = (\pairs -> let
      (left, right) = unzip pairs
      part1 = sum . fmap abs $ zipWith (-) (sort left) (sort right)
      countProducts = M.intersectionWith (*) (counts left) (counts right)
      counts xs = M.fromList [(NE.head grp, NE.length grp) | grp <- NE.group . sort $ xs]
      similarityScores = M.mapWithKey (*) countProducts
      part2 = sum . M.elems $ similarityScores
    in show <$> [part1, part2])
}

-- DAY 2

remove1 :: [a] -> [[a]]
remove1 [] = []
-- Two cases:
-- 1) Remove the head and keep the rest of the list
-- 2) Keep the head and remove an element from the rest of the list
remove1 (x:xs) = xs:((x:) <$> remove1 xs)

day2 :: Solution [[Int]]
day2 = Solution {
  day = 2,
  parser = let intList = sepBy1 decimal hspace in sepEndBy intList newline <* eof,
  solver = (\reports -> let
      isSafePart1 [] = True
      isSafePart1 levels = strictlyOrdered && all (inRange (1, 3) . abs) diffs where
        diffs = zipWith (-) (tailSafe levels) levels
        strictlyOrdered = all (> 1) diffs || all (< 0) diffs
      part1 = length . filter isSafePart1 $ reports
      isSafePart2 levels = any isSafePart1 (levels:(remove1 levels))
      part2 = length . filter isSafePart2 $ reports
    in show <$> [part1, part2])
}

-- DAY 3
data Instruction = Mul [Int] | Enable | Disable deriving (Show)

mul :: Parser [Int]
mul = between "mul(" ")" (decimal `sepBy` char ',')

instruction :: Parser Instruction
instruction = choice [Mul <$> mul, Enable <$ "do()", Disable <$ "don't()"]

junk :: Parser String
-- Keep taking characters until we reach the start of a valid instruction.
junk = many $ notFollowedBy instruction *> anySingle

day3 :: Solution [Instruction]
day3 = Solution {
  day = 3,
  parser = optional junk *> instruction `sepEndBy` junk,
  solver = (\instructions -> let
      -- Only look at Mul instructions
      part1 = sum [product args | Mul args <- instructions]
      -- at each instruction, figure out whether Muls are enabled/disabled
      enabled :: [Bool] 
      enabled = tailSafe . scanl updateEnabled True $ instructions where
        updateEnabled prev (Mul _) = prev -- Muls don't change enabled/disabled state
        updateEnabled _ Enable = True
        updateEnabled _ Disable = False
      -- Only look at Mul instructions which are enabled
      part2 = sum [product args | (Mul args, True) <- zip instructions enabled]
    in show <$> [part1, part2])
}

-- DAY 4

-- O(n^2), could improve to linear by using a regex library
countSubsequences :: Eq a => [a] -> [a] -> Int
countSubsequences s = length . filter (isPrefixOf s) . tails

groupOn :: Eq b => (a -> b) -> [a] -> [[a]]
groupOn f = groupBy $ \a b -> f a == f b

countXmas :: [String] -> Int
countXmas rows = sum $ fmap (countSubsequences "XMAS") searchStrings where
  searchStrings = forwardStrings ++ (reverse <$> forwardStrings)
  forwardStrings = rows ++ cols ++ diagStrings 
  cols = transpose rows
  diagStrings = [[rows !! r !! c | (r, c) <- diag] | diag <- diagCoords]
  diagCoords = concat [sortAndGroupOn (uncurry f) coords | f <- [(-), (+)]] where
    coords = [(r, c) | r <- [0..length rows - 1], c <- [0..length cols - 1]]
    sortAndGroupOn f = groupOn f . sortOn f

countMasXs :: [String] -> Int
countMasXs rows = length . filter hasMasX $ coords where
  cols = transpose rows
  coords = [(r, c) | r <- [0..length rows - 3], c <- [0..length cols - 3]]
  hasMasX (r, c) = all (\d -> d == "SAM" || d == "MAS") diags where
      diags :: [String]
      diags = [[rows !! (r + dr) !! (c + dc) | (dr, dc) <- offsets] | offsets <- diagCoords]
      diagCoords = [
        [(0, 0), (1, 1), (2, 2)],
        [(0, 2), (1, 1), (2, 0)]]

day4 :: Solution [String]
day4 = Solution {
  day = 4,
  parser = lines <$> takeRest,
  solver = (\rows -> show <$> [countXmas rows, countMasXs rows])
}

-- DAY 5

day5 :: Solution ([(Int, Int)], [[Int]])
day5 = Solution {
  day = 5,
  parser = let
      edge = (,) <$> decimal <* char '|' <*> decimal
      nodeList = decimal `sepBy1` char ','
    in (,) <$> edge `sepEndBy` newline <* newline <*> nodeList `sepEndBy` newline,
  solver = \(edges, nodeLists) -> let
      isCoveredBy a b = elem (a, b) edges
      inOrder [] = True
      inOrder (x:xs) = none (`isCoveredBy` x) xs && inOrder xs
      middle xs = xs !! (length xs `div` 2)
      part1 = sum . fmap middle . filter inOrder $ nodeLists
      -- Very inefficient O(E*V^2) topsort, where E is length of edges and
      -- V is length of the argument node/vertex list
      topsort [] = []
      topsort xs = source:(topsort (delete source xs)) where
        source = fromJust $ find (\x -> none (`isCoveredBy` x) xs) xs
      part2 =  sum $ fmap (middle . topsort) . filter (not . inOrder) $ nodeLists
    in show <$> [part1, part2]
}

-- DAY 6

type Coord = (Int, Int)

data Pose = Pose {
    _position :: (Int, Int)
  , _direction :: (Int, Int)
} deriving (Eq, Ord, Show)
makeLenses ''Pose

-- +y is down and +x is right
turnRight :: Num a => (a, a) -> (a, a)
turnRight (y, x) = (x, -y)

addTuples :: (Num a, Num b) => (a, b) -> (a, b) -> (a, b)
addTuples (a0, b0) (a1, b1) = (a0 + a1, b0 + b1)

day6Step :: S.Set Coord -> Pose -> Pose
day6Step obstacles pose = update pose where
  update = if blocked then direction %~ turnRight else position .~ inFront
  inFront = addTuples (pose ^. position) (pose ^. direction)
  blocked = S.member inFront obstacles

hasDuplicate :: Ord a => [a] -> Bool
hasDuplicate = help S.empty where
  help _ [] = False
  help seen (x:xs) = if S.member x seen then True else help (S.insert x seen) xs

elemIndices2d :: Eq a => a -> [[a]] -> [(Int, Int)]
elemIndices2d x xs = do
  (rowIdx, row) <- zip [0..] xs
  colIdx <- elemIndices x row
  return (rowIdx, colIdx)

data Day6Input = Day6Input {
    mapSize :: (Int, Int)
  , obstacles :: S.Set (Int, Int)
  , start :: Pose
} deriving (Eq, Show)

day6 :: Solution Day6Input
day6 = Solution {
    day = 6
  , parser = do
      rows <- lines <$> takeRest -- bypass megaparsec for this day
      let caretCoords = elemIndices2d '^' rows
      case caretCoords of
        [caretCoord] -> return Day6Input {
              mapSize = (length rows, length $ transpose rows)
            , obstacles = S.fromList $ elemIndices2d '#' rows
            , start = Pose {
                _position = caretCoord
                -- +y is down and +x is right
              , _direction = (-1, 0) 
            }
          }
        _ -> fail $ "Expected exactly one '^' but found " ++ show (length caretCoords)
  , solver = \Day6Input{mapSize, obstacles, start} -> let
      onMap (y, x) = inRange (0, fst mapSize - 1) y && inRange (0, snd mapSize - 1) x
      part1Positions :: S.Set (Int, Int)
      part1Positions = iterate (day6Step obstacles) start -- [Pose]
        <&> view position -- [(Int, Int)]
         &  takeWhile onMap
         &  S.fromList
      part1 = S.size part1Positions
      -- Instead of trying putting an obstacle at any empty space,
      -- only test spaces the guard would actually run into an obstacle.
      obstacleCandidates :: S.Set (Int, Int)
      obstacleCandidates = S.delete (start ^. position)  part1Positions
      -- If we're ever in the same pose a second time, we know the simulation
      -- is in a loop.
      inducesLoop newObstacle = hasDuplicate poses where
        poses :: [Pose]
        poses = iterate (day6Step (S.insert newObstacle obstacles)) start
          & takeWhile (onMap . view position)
      part2 = length $ S.filter inducesLoop obstacleCandidates
    in show <$> [part1, part2]
}
 
-- DAY 7

reductions :: [a -> a -> a] -> [a] -> [a]
reductions _ [] = []
reductions ops xs = foldl1 (\a b -> ops <*> a <*> b) (pure <$> xs)

numDigits :: (Integral a) => a -> a
numDigits 0 = 0
numDigits n = 1 + numDigits (n `div` 10)

catDigits :: Int -> Int -> Int
catDigits a b = a * (10 :: Int)^(numDigits b :: Int) + b where

day7 :: Solution [(Int, [Int])]
day7 = Solution {
    day = 7
  , parser = ((,) <$> decimal <* ": " <*> decimal `sepBy` " ") `sepEndBy` newline
  , solver = \equations -> let
      solvableWith ops (target, operands) = target `elem` reductions ops operands
      part1 = sum . fmap fst . filter (solvableWith [(+), (*)]) $ equations
      part2 = sum . fmap fst . filter (solvableWith [catDigits, (+), (*)]) $ equations
    in show <$> [part1, part2]
}

-- DAY 8

pairs :: [a] -> [(a, a)]
pairs [] = []
pairs (x:xs) = ((x,) <$> xs) ++ pairs xs

subTuples :: Num a => (a, a) -> (a, a) -> (a, a)
subTuples a b = addTuples a (over both negate b)

antinodes1 :: Integral a => (a, a) -> (a, a) -> [(a, a)]
antinodes1 x y = outsides ++ insides where
  diff = subTuples y x
  -- outsides are like o---x---y---o
  outsides = [addTuples y diff, subTuples x diff]
  -- insides are like x--o--o--y
  insides = if allOf both ((== 0) . (`mod` 3)) diff
    then let diffDiv3 = over both (`div` 3) diff
      in [addTuples x diffDiv3, subTuples y diffDiv3]
    else []

antinodes2 :: Integral a => ((a, a) -> Bool) -> (a, a) -> (a, a) -> [(a, a)]
antinodes2 onMap x y = help x y ++ help y x where
  -- given            a--b----...
  -- returns antinodes   o--o--o--o--...
  help a b = takeWhile onMap [addTuples b (over both (*n) diff) | n <- [0..]] where
    diff = subTuples b a

countUnique :: (Foldable t, Ord a) => t a -> Int
countUnique = S.size . S.fromList . toList 

day8 :: Solution ((Int, Int), M.Map Char [(Int, Int)])
day8 = Solution {
    day = 8
  , parser = do
      rows <- lines <$> takeRest -- bypass megaparsec for today
      let charLocs = [ (c, (i, j)) 
                     | (i, row) <- zip [0..] rows
                     , (j, c) <- zip [0..] row
                     , c /= '.'
                     ]
          mapSize = (length rows, length $ head rows)
      return $ (mapSize, MM.toMap $ MM.fromList charLocs)
  , solver = \((rows, cols), charLocs) -> let
      onMap (r, c) = inRange (0, rows - 1) r && inRange (0, cols - 1) c
      allPairs = M.elems charLocs >>= pairs
      part1 = countUnique [x | (a, b) <- allPairs, x <- antinodes1 a b, onMap x]
      part2 = countUnique [x | (a, b) <- allPairs, x <- antinodes2 onMap a b]
    in [show part1, show part2]
}
   
-- DAY 9
interleave :: [[a]] -> [a]
interleave = concat . transpose

readDiskMap :: [Int] -> [Chunk]
readDiskMap sizes = [Chunk{size, fileId} | (size, fileId) <- zip sizes ids] where
  ids = interleave [Just <$> [0..], repeat Nothing]

expandDiskMap :: [Chunk] -> [Maybe Int]
expandDiskMap chunks = [fileId  | Chunk{size, fileId} <- chunks, _ <- [1..size]]

compact1 :: [Maybe Int] -> [Int]
compact1 = help . Seq.fromList where
  help Empty = []
  help (Nothing:<|Empty) = [] -- single free space
  help (Just x:<|Empty) = [x] -- single file block
  help (a:<|(middle:|>b)) = case (a, b) of
    (_, Nothing) -> help (a <| middle) -- discard trailing free space
    (Just x, _) -> x:help (middle |> b) -- leave leading file blocks alone
    (Nothing, Just x) -> x:help middle -- move trailing file blocks to free space

compact2 :: [Chunk] -> [Chunk]
compact2 = toList . help . Seq.fromList where
  help Empty = Empty
  help (prefix:|>x@Chunk{fileId=Nothing}) = (help prefix) |> x
  help (prefix:|>x) = case attemptInsert x prefix of
    Just result -> help result |> Chunk{fileId=Nothing, size=size x}
    Nothing -> help prefix |> x
  attemptInsert _ Empty = Nothing
  attemptInsert x (y:<|suffix) = case fileId y of
    Just _ -> fmap (y<|) (attemptInsert x suffix)
    Nothing -> case compare (size x) (size y) of
      LT -> Just $ x <| Chunk{fileId=Nothing, size=size y - size x} <| suffix
      EQ -> Just $ x <| suffix
      GT -> fmap (y<|) (attemptInsert x suffix)

data Chunk = Chunk {
    fileId :: Maybe Int
  , size :: Int
} deriving (Show)

day9 :: Solution [Chunk]
day9 = Solution {
    day = 9
  , parser = readDiskMap <$> many (digitToInt <$> digitChar)
  , solver = \chunks -> let
      checksum = sum . zipWith (*) [0..]
      part1 = checksum . compact1 . expandDiskMap $ chunks 
      part2 = checksum . fmap (fromMaybe 0) . expandDiskMap . compact2 $ chunks
    in show <$> [part1, part2]
}

  
-- DAY 10

(!!?) :: [[a]] -> (Int, Int) -> Maybe a
grid !!? (row, col) = grid !? row >>= (!? col)

depthFirstSearch :: ((Int, Int) -> s -> s) -> ((Int, Int) -> s -> Bool) -> (Int, Int) -> [[Int]] -> State s Int
depthFirstSearch visit visited coord@(row, col) grid = do
  let height = grid !! row !! col
      neighbors = [ neighbor
                  | offset <- [(0, 1), (0, -1), (1, 0), (-1, 0)]
                  , let neighbor = coord ^+^ offset
                  , Just neighborHeight <- [grid !!? neighbor]
                  , neighborHeight == height + 1 ]
      trailsFromNeighbors = sequence [depthFirstSearch visit visited n grid | n <- neighbors]
  alreadyVisited <- gets (visited coord)
  if alreadyVisited then return 0
  else do
    modify (visit coord)
    if height == 9 then return 1 else sum <$> trailsFromNeighbors

day10 :: Solution [[Int]]
day10 = Solution {
    day = 10
  , parser = some (digitToInt <$> digitChar) `sepEndBy1` newline
  , solver = \grid -> let
      part1 = sum [ evalState (depthFirstSearch S.insert S.member (r, c) grid ) S.empty
        | r <- [0..length grid - 1]
        , c <- [0..length (head grid) - 1]
        , grid !! r !! c == 0
        ]
      const2 a _ _ = a
      part2 = sum [ evalState (depthFirstSearch (const2 ()) (const2 False) (r, c) grid ) ()
        | r <- [0..length grid - 1]
        , c <- [0..length (head grid) - 1]
        , grid !! r !! c == 0
        ]

    in show <$> [part1, part2]
}

-- DAY 11

day11 :: Solution [Int]
day11 = Solution {
    day = 11
  , parser = decimal `sepBy` " "
  , solver = \stones -> let
      state0 :: IM.IntMap Int
      state0 = IM.fromListWith (+) [(x, 1) | x <- stones]
      tupleToList (a, b) = [a, b]
      step :: Int -> [Int]
      step 0 = [1]
      step x = case numDigits x :: Int of
        d | even d -> tupleToList $ divMod x (10^(d `div` 2))
          | otherwise -> [2024 * x]
      stepAll xs = IM.fromListWith (+) [(x', count) | (x, count) <- IM.toList xs, x' <- step x]
      states = iterate stepAll state0
      part1 = sum . IM.elems $ states !! 25
      part2 = sum . IM.elems $ states !! 75
    in show <$> [part1, part2]
}

-- DAY 12

-- data PlotDimensions = PlotDimensions {
--     area :: Int
--   , fenceLength :: Int
-- }
-- dfs :: [String] -> Char -> S.Set (Int, Int) -> (Int, Int) -> Maybe (S.Set (Int, Int), (Int, Int))
-- dfs grid plantType visited coord = let
--   directions = [(1, 0), (-1, 0), (0, 1), (0, -1)]
--   neighbors = [(x, coord') | coord' <- [coord ^+^ d | d <- directions], Just x <- [grid !!? coord']]
--   fence = length [() | (x, _) <- neighbors, x /= plantType]
  
up = (-1, 0)
down = (1, 0)
left = (0, -1)
right = (0, 1)

minBy f x y = if (f x <= f y) then x else y
pairwise :: [a] -> [(a, a)]
pairwise xs = zip xs (tail xs)

dfs :: [String] -> (Int, Int) -> Char -> State (S.Set (Int, Int)) (Maybe (Int, Int, Int))
dfs grid start c = do
  visited <- gets (S.member start)
  if visited then
    return Nothing
  else do
    modify $ S.insert start
    let neighbors = [start ^+^ step | step <-[up, down, left, right]]
        fenceCount = length $ filter ((/= Just c) . (grid !!?)) neighbors
        corners = pairwise [up, right, down, left, up]
        isCorner :: (Int, Int) -> (Int, Int) -> Bool
        isCorner a b = let
            aSame = grid !!? (start ^+^ a) == Just c
            bSame = grid !!? (start ^+^ b) == Just c
            abSame = grid !!? (start ^+^ a ^+^ b) == Just c
          in case (aSame, bSame, abSame) of
            (True, True, False) -> True
            (False, False, _) -> True
            _ -> False
        cornerCount = length $ filter (uncurry isCorner) corners
        samePlot = [(idx, value) | idx <- neighbors, Just value <- [grid !!? idx], value == c]
    searchResults <- traverse (uncurry (dfs grid)) samePlot
    return . Just $ (fenceCount, cornerCount, 1) ^+^ sumV (catMaybes searchResults)

day12 :: Solution [String]
day12 = Solution {
    day = 12
  , parser = lines <$> takeRest
  , solver = \grid -> let
      coords = [(i, j) | (i, row) <- zip [0..] grid, j <- [0..length row - 1]]
      plotStats = catMaybes . flip evalState S.empty . sequenceA  $ [dfs grid (r, c) (grid !! r !! c) | (r, c) <- coords]
      part1 = sum . fmap (\(fences, _, area) -> fences * area) $ plotStats
      part2 = sum . fmap (\(_, corners, area) -> corners * area) $ plotStats
    in show <$> [part1, part2]
}

-- DAY 13

day13 :: Solution [(M22 Int, V2 Int)]
day13 = Solution {
    day = 13
  , parser = let
      equation = do
        buttonA <- V2 <$> ("Button A: X+" *> decimal) <*> (", Y+" *> decimal) <* newline
        buttonB <- V2 <$> ("Button B: X+" *> decimal) <*> (", Y+" *> decimal) <* newline
        prize <- V2 <$> ("Prize: X=" *> decimal) <*> (", Y=" *> decimal)
        return $ (LM.transpose (V2 buttonA buttonB), prize)
    in equation `sepEndBy1` (many newline)
  , solver = \equations -> let
      cost = dot $ V2 3 1
      solve1d a b c = help a b ++ help b a where
        help x y = take 1 
          [ V2 i j 
          | i <- [0..x]
          , let (j, rem) = (c - i * x) `divMod` y
          , rem == 0
          ]
      solve :: M22 Int -> V2 Int -> [V2 Int]
      solve m y = if det22 m /= 0 then 
          let solution = luSolveFinite (fmap (fmap fromIntegral) m) (fmap fromIntegral y) in
            if (denominator <$> solution) == V2 1 1 then 
              [numerator <$> solution] 
            else []
        else solve1d (sum (m ^. column _1)) (sum (m ^. column _2)) (sum y)
      part1 = sum . catMaybes $ 
        [ minimumMay [cost s | s <- solve m target] 
        | (m, target) <- equations
        ]
      part2 = sum . catMaybes $ 
        [ minimumMay [cost s | s <- solve m ((10000000000000+) <$> target)] 
        | (m, target) <- equations
        ]
      solutions = [solve m target | (m, target) <- equations]
    in show <$> [part1, part2]
}


-- DAY 14

day14 :: Solution [M22 Int]
day14 = Solution {
    day = 14
  , parser = let
      int = signed (pure ()) decimal
      intPair = V2 <$> int <* "," <*> int
      pv = V2 <$> ("p=" *> intPair) <*> (" v=" *> intPair)
    in sepEndBy1 pv newline
  , solver = \state0 -> let
      bounds = V2 101 103
      middle = (`div` 2) <$> bounds
      steps = [[mod <$> p + (i *^ v) <*> bounds | V2 p v <- state0] | i <- [0..]]
      safetyFactor robotPositions = let
          region p = compare <$> middle <*> p
          countByRegion = M.fromListWith (+) [(region p, 1) | p <- robotPositions]
        in product [count | (r, count) <- M.toList countByRegion, none (== EQ) r]
      part1 = safetyFactor (steps !! 100)

      visualize robotPositions = let
          V2 cols rows = bounds
          charForPosition p = if elem p robotPositions then '█' else ' '
        in unlines [[charForPosition (V2 x y) | x <- [0..cols-1]] | y <- [0..rows-1]]
      variance positions = sum squaredDifferences `div` n where
        n = length positions
        squaredDifferences = [quadrance (p - mean) | p <- positions]
        mean = (`div` n) <$> sum positions
      candidates = take 5 $ sortOn (variance . snd) (zip [0..] (take 10000 steps))
      part2 = unlines 
        [ concat ["Step ", show i, "\n", visualize positions, "\n"] 
        | (i, positions) <- candidates
        ]
    in [show part1, part2]
}

-- DAY 15

data Cell = Robot | Box | Wall deriving (Eq, Show)


flattenGrid :: [[a]] -> [(V2 Int, a)]
flattenGrid xs = [(V2 r c, x) | ((r, c), x) <- itoListOf (ifolded <.> ifolded) xs]

forEach :: Foldable t => t a -> b -> (b -> a -> b) -> b
forEach xs initial f = foldl f initial xs

charToCell = [('#', Wall), ('O', Box), ('@', Robot)]
swap (a, b) = (b, a)
cellToChar :: Cell -> Char
cellToChar c = fromJust . lookup c . fmap swap $ charToCell

day15part1 :: M.Map (V2 Int) Cell -> [V2 Int] -> Int
day15part1 warehouse0 moves = let
    move :: V2 Int -> V2 Int -> M.Map (V2 Int) Cell -> M.Map (V2 Int) Cell
    move from to warehouse = M.insert to (warehouse ! from) (M.delete from warehouse)
    push :: V2 Int -> V2 Int -> M.Map (V2 Int) Cell -> M.Map (V2 Int) Cell
    push coord dir warehouse = flip execState warehouse $ do
      cell <- gets (M.lookup coord)
      case cell of
        Nothing -> return ()
        Just Wall -> return ()
        _ -> do
          let inFront = coord + dir
          modify $ push inFront dir
          cantMove <- gets (M.member inFront)
          if cantMove then return () else modify $ move coord inFront

    visualize :: M.Map (V2 Int) Cell -> String
    visualize warehouse = unlines [[charForCoord (V2 r c) | c <- [0..maxCol]] | r <- [0..maxRow]] where
      charForCoord c = fromMaybe '.' (cellToChar <$> M.lookup c warehouse)
      maxRow = maximum . fmap (^._1) . M.keys $ warehouse
      maxCol = maximum . fmap (^._2) . M.keys $ warehouse
    gps :: V2 Int -> Int
    gps = dot (V2 100 1)
    step warehouse dir = push robot dir warehouse where
      robot = head [coord | (coord, Robot) <- M.toList warehouse]
    states = scanl step warehouse0 moves 
  in sum [gps coord | (coord, Box) <- M.toList (last states)]

day15part2 warehouse0 moves = let
    expandedWarehouse0 = 
      [ (V2 (V2 r (2 * c)) (V2 1 width), cell) 
      | (V2 r c, cell) <- M.toList warehouse0
      , let width = if cell == Robot then 1 else 2
      ]
    inRegion coord (V2 corner size) = and ((<=) <$> corner <*> coord) && and ((<) <$> coord <*> corner + size) 
    findAndDeleteAt :: V2 Int -> StateT [(M22 Int, Cell)] Maybe (M22 Int, Cell)
    findAndDeleteAt coord = do
      warehouse <- get 
      x <- lift $ find (inRegion coord . fst) warehouse
      modify $ delete x
      return x
    intersects1d :: V2 Int -> V2 Int -> Bool
    intersects1d (V2 a1 a2) (V2 b1 b2) = b1 < a2 && a1 < b2
    intersects :: M22 Int -> M22 Int -> Bool
    intersects a b = and [intersects1d (range r a) (range r b) | r <- [_x, _y]] where
      range axis bbox = V2 a (a + da) where
        V2 a da = bbox ^. column axis

    visualize warehouse = let
        lowerRightCorners = [bbox^._1 + bbox^._2 | (bbox, _) <- warehouse]
        rowMax = maximum . fmap (^._1) $ lowerRightCorners
        colMax = maximum . fmap (^._2) $ lowerRightCorners
      in unlines [ [ case cell of Just Robot -> '@'; Just Wall -> '#'; Just Box -> 'O'; Nothing -> '.'
             | c <- [0..colMax]
             , let cell = snd <$> find (inRegion (V2 r c) . fst) warehouse]
           | r <- [0..rowMax]
           ]
    push :: V2 Int -> V2 Int -> StateT [(M22 Int, Cell)] Maybe ()
    push coord dir = do
      (bbox, cell) <- findAndDeleteAt coord
      guard $ cell /= Wall
      let bbox' = bbox & _1 %~ (+ dir)
      obstacles <- gets $ filter ((intersects bbox') . fst)
      forM_ obstacles (\((V2 corner  _), _) -> push corner dir)
      modify ((bbox', cell):)

    step :: [(M22 Int, Cell)] -> V2 Int -> [(M22 Int, Cell)]
    step warehouse dir = let
        Just (V2 robotCoord _, _) = find ((== Robot) . snd) warehouse
        pushResult = execStateT (push robotCoord dir) warehouse
      in fromMaybe warehouse pushResult
    states = scanl step expandedWarehouse0 moves 
  in sum [dot (V2 100 1) corner | (V2 corner _, Box) <- last states]
  
  

day15 :: Solution (M.Map (V2 Int) Cell, [V2 Int])
day15 = Solution {
    day = 15
  , parser = do
      let validMapChars = '.':(fst <$> charToCell)
      grid <- many (oneOf validMapChars) `sepBy1` newline 
      let coordToChar = M.fromList (flattenGrid grid)
          coordToCell = mapMaybe (`lookup` charToCell) coordToChar 
      let charToMove = [('^', V2 (-1) 0), ('v', V2 1 0), ('<', V2 0 (-1)), ('>', V2 0 1)]
          validMoveChars = fst <$> charToMove
      moveString <- some $ (try (many newline *> oneOf validMoveChars))
      let moves = mapMaybe (`lookup` charToMove) moveString
      _ <- many newline
      return (coordToCell, moves)
  , solver = \(warehouse0, moves) -> [show $ f warehouse0 moves | f <- [day15part1, day15part2]]
}

-- DAY 16


dijkstras :: (Foldable t, Ord n, Ord c, Monoid c, Show n, Show c) => (n -> t (n, c)) -> n -> M.Map n c
dijkstras outs start = go (S.singleton (mempty, start)) M.empty where
  go queue result = case S.minView queue of
    Nothing -> result
    Just ((c, n), queue') 
      | M.member n result -> go queue' result
      | otherwise -> let
         newQueueMembers = S.fromList [(c <> c', n') | (n', c') <- toList (outs n)]
       in go (S.union newQueueMembers queue') (M.insert n c result)

dijkstrasAllPaths :: (Foldable t, Ord n, Ord c, Monoid c, Show n, Show c) => (n -> t (n, c)) -> n -> M.Map n (c, [[n]])
dijkstrasAllPaths outs start = go (S.singleton (mempty, [start])) M.empty where
  go queue result = case S.minView queue of
    Nothing -> result
    Just ((c, path@(n:ns)), queue') -> let
        newQueueMembers = S.fromList [(c <> c', (n':path)) | (n', c') <- toList (outs n)]
        queue'' = S.union newQueueMembers queue'
      in case M.lookup n result of
        Nothing -> go queue'' (M.insert n (c, [path]) result)
        Just (minCost, paths) 
          | c == minCost -> go queue'' (M.adjust (_2 %~ (path:)) n result)
          | otherwise -> go queue' result

day16 :: Solution (S.Set (V2 Int), V2 Int, V2 Int)
day16 = Solution {
    day = 16
  , parser = do
      grid <- flattenGrid . lines <$> takeRest
      let walkable = S.fromList [coord | (coord, c) <- grid, c /= '#']
          start = head [coord | (coord, 'S') <- grid]
          end = head [coord | (coord, 'E') <- grid]
      return (walkable, start, end)
  , solver = \(walkable, start, end) -> let
      outEdges :: M22 Int -> [(M22 Int, (Sum Int))]
      outEdges (V2 coord dir) = forward ++ [turnLeft, turnRight] where
        forward = if S.member (coord + dir) walkable 
          then [(V2 (coord + dir) dir, Sum 1)]
          else []
        turnLeft = (V2 coord (perp dir), Sum 1000)
        turnRight = (V2 coord (negate $ perp dir), Sum 1000)
      costs :: M.Map (M22 Int) (Sum Int)
      costs = dijkstras outEdges (V2 start (V2 0 1))
      part1 = minimum [getSum cost | (V2 coord _, cost) <- M.toList costs, coord == end]

      allPaths = dijkstrasAllPaths outEdges (V2 start (V2 0 1))
      pathsToEnd = [ path & mapped %~ (^. _1)
                   | ((V2 coord _), (_, paths)) <- M.toList allPaths
                   , coord == end
                   , path <- paths
                   ]
      part2 = countUnique . concat $ pathsToEnd
    in [show part1, show part2]
}

-- DAY 17

line = many (anySingleBut '\n') <* newline

day17 :: Solution (Int, [Int])
day17 = Solution {
    day = 17
  , parser = do
      a <- "Register A: " *> decimal <* newline
      _ <- sequenceA [line, line, line]
      program <- "Program: " *> (decimal `sepBy` ",")
      return $ (a, program)
  , solver = \(a0, program) -> let
      output a = let
          b = (a .&. 0b111) .^. 0b011
          c = ((a .>>. b) .&. 0b111) .^. 0b101
        in b .^. c
      step 0 = Nothing
      step a = Just (output a, a .>>. 3)
      search :: Int -> [Int] -> [Int]
      search a [] = [a]
      search a (x:xs) = [ result 
                        | i <- [0..7]
                        , let a' = (a .<<. 3) + i
                        , output a' == x
                        , result <- search a' xs
                        ]
      part1 = unfoldr step a0
      part2 = head $ search 0 (reverse program)
    in [show part1, show part2]
}

-- DAY 18
bfs :: (Foldable t, Ord a) => (a -> t a) -> a -> [S.Set a]
bfs neighbors start = unfoldr step (S.singleton start, S.empty) where
  step (frontier, visited) 
    | S.null frontier = Nothing
    | otherwise = Just (frontier, (frontier', visited')) where
      visited' = S.union frontier visited
      frontier' = S.fromList (concat [ toList (neighbors n) | n <- toList frontier]) S.\\ visited'

existsPath :: (Foldable t, Ord a) => (a -> t a) -> a -> a -> Bool
existsPath neighbors start end = evalState (canReachEndFrom start) S.empty where
  canReachEndFrom n 
    | n == end = return True
    | otherwise = do
        visited <- gets $ S.member n
        if visited then
          return False
        else do
          modify $ S.insert n
          anyM canReachEndFrom (neighbors n)

partitionPoint :: (a -> Bool) -> [a] -> Maybe Int
partitionPoint p xs = if result == length xs then Nothing else Just result where
  result = go 0 (length xs)
  go lo hi
    | lo == hi = lo
    | otherwise = let
        mid = (lo + hi) `div` 2
      in if p (xs !! mid) 
        then go (mid + 1) hi
        else go lo mid
           
anyM :: (Foldable t, Monad m) => (a -> m Bool) -> t a -> m Bool
anyM predicate xs = isJust <$> findM predicate xs

findM :: (Foldable t, Monad m) => (a -> m Bool) -> t a -> m (Maybe a)
findM predicate xs = go (toList xs) where
  go [] = return Nothing
  go (y:ys) = do
    found <- predicate y
    if found 
      then return $ Just y
      else go ys
  
day18 :: Solution [V2 Int]
day18 = Solution {
    day = 18
  , parser = (V2 <$> decimal <* ","  <*> decimal) `sepEndBy1` newline
  , solver = \obstacles -> let
      mapSize = 70
      bounds = V2 mapSize mapSize
      inBounds x = and ((<=) <$> zero <*> x) && and ((<=) <$> x <*> bounds)
      dirs = [V2 0 1, V2 1 0, V2 0 (-1), V2 (-1) 0]
      obstacleSets = tailSafe $ scanl (flip S.insert) S.empty obstacles 
      reachableNeighbors obstacles coord = 
        [ coord' 
        | step <- dirs, 
        let coord' = coord + step
        , inBounds coord'
        , not $ S.member coord' obstacles
        ]
      part1 = findIndex (S.member bounds) (bfs getNeighbors zero) where
        getNeighbors = reachableNeighbors (obstacleSets !! 1024)

      -- Part 2 Approach 1: Linear Search with Union-Find
      mapSpan = S.fromList [0..70]
      isBlockingPath :: S.Set (V2 Int) -> Bool
      isBlockingPath xs = or [ eq1 mapSpan (over setmapped (^. dim) xs) | dim <- [_x, _y]]
      addingBlocksPath :: V2 Int -> State [S.Set (V2 Int)] Bool
      addingBlocksPath o = do
        let neighbors = S.fromList [ o + (V2 dx dy) 
                                   | dx <- [-1..1]
                                   , dy <- [-1..1]
                                   , dx /= 0 || dy /= 0
                                   ]
        (otherGroups, connectedToO) <- gets $ partition (S.disjoint neighbors)
        let newGroup = S.insert o (S.unions connectedToO)
        put $ newGroup:otherGroups
        return $ isBlockingPath newGroup
      blockList = evalState (traverse addingBlocksPath obstacles) []
      part2 = evalState (findM addingBlocksPath obstacles) []

      -- Part 2, Approach 2: Binary Search with Depth First Search
      openAtStep = [ existsPath getNeighbors zero bounds 
                   | obstacles <- obstacleSets
                   , let getNeighbors = reachableNeighbors obstacles
                   ]
      firstBlockIdx = partitionPoint id openAtStep
      part2' = (obstacles !!) <$> firstBlockIdx

    in [show part2']
}

-- DAY 19

day19 :: Solution ([String], [String])
day19 = Solution {
    day = 19
  , parser = do
    let pattern = some (oneOf ("wubrg" :: String))
    towels <- pattern `sepBy` ", "
    _ <- some newline
    designs <- pattern `sepEndBy1` newline
    return (towels, designs)
  , solver = \(towels, designs) -> let
      numArrangements :: String -> Int
      numArrangements design = head $ go design where
        go "" = [1]
        go x@(_:rest) = (sum [countWithPrefix t | t <- towels]):suffixCounts where
          suffixCounts = go rest
          countWithPrefix t 
            | t `isPrefixOf` x = suffixCounts !! (length t - 1)
            | otherwise = 0

      part1 = length . filter ((/= 0) . numArrangements) $ designs
      part2 = sum . fmap numArrangements $ designs
    in [show part1, show part2]
}

 -- DAY 20

l1Diamond :: Int -> S.Set (V2 Int)
l1Diamond n = S.fromList . concat . take 4 $ iterate (fmap perp) [V2 x (n - x) | x <- [0..n]]

l1Norm = sum . fmap abs
l1Dist a b = l1Norm (a - b)

day20 = Solution {
    day = 20
  , parser = do
      grid <- flattenGrid . lines <$> takeRest
      let start = head [coord | (coord, 'S') <- grid] 
          end = head [coord | (coord, 'E') <- grid]
          walkable = S.fromList [coord | (coord, x) <- grid, elem x (".SE" :: String)]
      return (start, end, walkable)
  , solver = \(start, end, walkable) -> let
      -- computes the set of nodes n steps away from node x
      stepsAwayFrom n x = S.intersection (S.mapMonotonic (x + ) (l1Diamond n)) walkable
      -- bfs returns a [S.Set (V2 Int)], essential a mapping from (distance from start -> set of coords)
      -- this converts to a mapping from (coord -> distance from start)
      indexByCoord :: [S.Set (V2 Int)] -> M.Map (V2 Int) Int
      indexByCoord steps = M.fromList [ (coord, dist) 
                                      | (dist, frontier) <- zip [0..] steps
                                      , coord <- toList frontier]
      -- If we know the distances start->n0 and n1->end, we can figure out the
      -- potential savings of phasing through walls from n0->n1
      distFromStart = indexByCoord $ bfs (1 `stepsAwayFrom`) start
      distToEnd = indexByCoord $ bfs (1 `stepsAwayFrom`) end
      baseline = distFromStart ! end
      -- amount saved by phasing from n0 to n1
      shortcutSavings n0 n1 = baseline - newCost where
        newCost = (distFromStart ! n0) + l1Dist n1 n0 + (distToEnd ! n1)
      -- computes the savings from phasing between all pairs of nodes within
      -- manhattan distance of 20 of eachother
      cheats = [ (duration, shortcutSavings n0 n1)
               | n0 <- toList walkable
               , n1 <- toList walkable
               , let duration = l1Dist n1 n0
               , duration <= 20
               ]
      part1 = length [stepsSaved | (2, stepsSaved) <- cheats, stepsSaved >= 100]
      savings = snd <$> cheats
      part2 = length $ filter (>= 100) savings
    in [show part1, show part2]
}

-- DAY 21

day21 :: Solution [String]
day21 = Solution {
    day = 21
  , parser = lines <$> takeRest
  , solver = \codes -> let
      solve levels = sum [complexity c | c <- codes] where
        finalKeypadCost = iterate (keyCost keypad) M.empty !! levels
        numpadCost = keyCost numpad finalKeypadCost
        complexity code = codeCost numpadCost code * numericPart code
        numericPart code = read (takeWhile isDigit code) :: Int
      part1 = solve 2
      part2 = solve 25
    in [show part1, show part2]
}

project :: V2 Int -> Lens' (V2 Int) Int -> V2 Int
project v axis = zero & axis .~ (v ^. axis)

findIndex2d :: Eq a => a -> [[a]] -> Maybe (V2 Int)
findIndex2d x xs = flattenGrid xs
   & find (\y -> snd y == x)
  <&> fst

numpad = [ "789"
         , "456"
         , "123"
         , " 0A"
         ]
keypad = [ " ^A"
         , "<v>"
         ]

codeCost :: M.Map (Char, Char) Int -> String -> Int
codeCost moveCost code = sum [ M.findWithDefault 1 pair moveCost 
                             | pair <- pairwise ('A':code)]

keyCost :: [String] -> M.Map (Char, Char) Int -> M.Map (Char, Char) Int
keyCost layout parentCost = M.fromList $ do
  let keys = [key | row <- layout, key <- row, key /= ' ']
  (key0, key1) <- (,) <$> keys <*> keys
  let parentCodeCosts = [ codeCost parentCost (path ++ "A")
                        | path <- paths layout key0 key1
                        ]
  return ((key0, key1), minimum parentCodeCosts)


paths :: [String] -> Char -> Char -> [String]
paths layout key0 key1 = let
    coord0 = fromJust $ findIndex2d key0 layout
    coord1 = fromJust $ findIndex2d key1 layout
    delta@(V2 dr dc) = coord1 - coord0
    rKey = if dr < 0 then '^' else 'v'
    cKey = if dc < 0 then '<' else '>'
    validKeyAt (V2 r c) = layout !! r !! c /= ' '
    rKeys = replicate (abs dr) rKey
    cKeys = replicate (abs dc) cKey
  in nub $ (if validKeyAt (coord0 + (V2 dr 0)) then [rKeys ++ cKeys] else []) ++
           (if validKeyAt (coord0 + (V2 0 dc)) then [cKeys ++ rKeys] else [])


-- DAY 22

stepSecret :: Int -> Int
stepSecret x = foldl substep x [(.<<. 6), (.>>. 5), (.<<. 11)] where
  substep :: Int -> (Int -> Int) -> Int
  substep n op = (op n .^. n) .&. 0xFFFFFF

slidingWindow :: Int -> [a] -> [[a]]
slidingWindow n xs = tails xs
                   & take n
                   & transpose
                   & takeWhile ((== n) . length)
                   
sequenceToPrice :: [Int] -> Map [Int] Int
sequenceToPrice prices = M.fromListWith (\_ b -> b) (zip sequences (drop 4 prices)) where
  priceDiffs = [b - a | (a, b) <- pairwise prices]
  sequences = slidingWindow 4 priceDiffs

day22 :: Solution [Int]
day22 = Solution {
    day = 22
  , parser = decimal `sepEndBy1` newline
  , solver = \initialSecrets -> let
      secretStreams = [take 2000 $ iterate stepSecret s0 | s0 <- initialSecrets]
      part1 = sum [last stream | stream <- secretStreams]
      prices = [[x `mod` 10 | x <- stream] | stream <- secretStreams]
      part2 = maximum $ foldl (M.unionWith (+)) M.empty [sequenceToPrice p | p <- prices]
    in [show part1, show part2]
}

-- DAY 23

day23 :: Solution [(String, String)]
day23 = Solution {
    day = 23
  , parser = let
      edge = (,) <$> some letterChar <* "-" <*> some letterChar
    in edge `sepEndBy1` newline
  , solver = \edgeList -> let
      nodes = setOf (each . each) edgeList
      neighbors :: M.Map String (S.Set String)
      neighbors = M.fromListWith (S.union) [ (n0, S.singleton n1) 
                                           | edge <- edgeList
                                           , (n0, n1) <- [edge, swap edge]
                                           ]
      cliquesBySize = iterate growCliques [S.empty]
      growCliques cliques = [ S.insert node clique 
                            | node <- toList nodes
                            , clique <- cliques
                            , all (< node) clique
                            , clique `S.isSubsetOf` (neighbors ! node)
                            ]
      part1 = length . filter (any (isPrefixOf "t")) $ cliquesBySize !! 3
      largestClique = head . last . takeWhile (not . null) $ cliquesBySize
      part2 = intercalate "," . sort . toList $ largestClique
    in [show part1, part2]
}

-- DAY 24
data Node a = Constant a Int | Assignment {
    result :: a
  , operands :: (a, a)
  , operator :: Int -> Int -> Int
}

nodeId (Constant x _) = x
nodeId (Assignment x _ _) = x

day24 :: Solution [Node String]
day24 = Solution {
   day = 24
 , parser = do
     let wire = some alphaNumChar
         constant = Constant <$> (wire <* ": ") <*> decimal
         bitop = ("AND" >> pure (.&.)) <|> ("XOR" >> pure (.^.)) <|> ("OR" >> pure (.|.))
         assignment = do
           in0 <- wire <* " "
           op <- bitop <* " "
           in1 <- wire <* " -> "
           out <- wire
           return $ Assignment out (in0, in1) op
     constants <- constant `sepEndBy` newline
     _ <- many newline
     assignments <- try assignment `sepEndBy` newline
     return $ constants ++ assignments
  , solver = \nodes -> let
      zs = sortOn Down . filter ("z" `isPrefixOf`) . fmap nodeId $ nodes
      lookupId x = fromJust . find ((== x) . nodeId) $ nodes
      evaluate x = let
        node = lookupId x
        in case node of
          Constant _ y -> y
          Assignment _ (a, b) op -> op (evaluate a) (evaluate b)
      part1 = foldl (\acc x -> (acc .<<. 1) .|. x) 0 (evaluate <$> zs)
    in [show part1]
}


-- DAY 25

day25 = Solution {
    day = 25
  , parser = do
      chunks <- some (notFollowedBy (newline *> newline) *> anySingle) `sepBy` (newline >> newline)
      let grids = lines <$> chunks
          (lockGrids, keyGrids) = partition (all (== '#') . head) grids
          locks = [[(subtract 1) . length . takeWhile (== '#') $ row | row <- transpose grid] | grid <- lockGrids]
          keys = [[(subtract 1) . length . takeWhile (== '#') . reverse $ row | row <- transpose grid] | grid <- keyGrids]
      return (locks, keys)
  , solver = \(locks, keys) -> let
      compatible key lock = all (< 6) $ zipWith (+) key lock
      part1 = length $ filter (uncurry compatible) [(l, k) | l <- locks, k <- keys]
    in [show part1]
}

