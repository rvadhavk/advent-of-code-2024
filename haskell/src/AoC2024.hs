module AoC2024 where

import Control.Monad (guard)
import Control.Monad.State.Lazy
import Control.Monad.Trans.Maybe
import Control.Lens hiding ((<|), (|>), Empty, levels)
import Data.AdditiveGroup
import Data.Char (digitToInt)
import Data.Foldable (toList)
import qualified Data.IntMap as IM
import Data.Ix (inRange)
import Data.List
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M
import Data.Maybe (catMaybes, fromMaybe)
import qualified Data.MultiMap as MM
import Data.Ratio
import qualified Data.Sequence as Seq
import Data.Sequence (Seq(..), (<|), (|>))
import qualified Data.Set as S
import Data.Maybe (fromJust)
import Data.Void (Void)
import Linear.V2
import Linear.V3
import Linear.Matrix hiding (transpose)
import Linear.Metric
import qualified Linear.Matrix as LM
import Linear.Vector ((*^))
import Safe
import Text.Megaparsec 
  ( Parsec
  , anySingle
  , between
  , choice
  , eof
  , errorBundlePretty
  , many
  , notFollowedBy
  , optional
  , parse
  , parseTest
  , sepBy
  , sepBy1
  , sepEndBy
  , sepEndBy1
  , some
  , takeRest
  )
import Text.Megaparsec.Char (char, digitChar, newline, hspace)
import Text.Megaparsec.Char.Lexer (decimal)


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
        diffs = zipWith (-) (drop 1 levels) levels
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
      enabled = drop 1 . scanl updateEnabled True $ instructions where
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
        help x y = take 1 [V2 i j | i <- [0..x], let (j, rem) = (c - i * x) `divMod` y, rem == 0]
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
    in [show part1, show part2]
}

