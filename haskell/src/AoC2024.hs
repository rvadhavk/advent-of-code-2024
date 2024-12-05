module AoC2024 where

import Data.Ix (inRange)
import Data.List
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.Void (Void)
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
  , takeRest
  )
import Text.Megaparsec.Char (char, newline, hspace)
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
      edge = (,) <$> decimal <* char '|' <*> decimal :: Parser (Int, Int)
      intList = decimal `sepBy1` char ',' :: Parser [Int]
    in (,) <$> edge `sepEndBy` newline <* newline <*> intList `sepEndBy` newline,
  solver = \(edges, nodeLists) -> let
      precedes a b = elem (a, b) edges
      inOrder [] = True
      inOrder (x:xs) = all (x `precedes`) xs && inOrder xs
      middle xs = xs !! (length xs `div` 2)
      part1 = sum . fmap middle . filter inOrder $ nodeLists
      -- Very inefficient O(n^3) topsort, but sufficient to solve the task in reasonable time
      topsort [] = []
      topsort xs = leaf:(topsort (delete leaf xs)) where
        leaf = fromJust $ find (\x -> not $ any (`precedes` x) xs) xs
      part2 =  sum $ fmap (middle . topsort) . filter (not . inOrder) $ nodeLists
    in show <$> [part1, part2]
}
