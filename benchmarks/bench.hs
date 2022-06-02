module Main where

import System.IO.Strict
import System.IO
import System.Process
import System.Environment
import System.Exit
import Control.Monad
import Text.Printf
import Formatting

-- The compiler configurations to be tested
-- givene as a triple of (name extensiton, description for stats reporting)
-- The first configuration is considered the baseline
conf :: [ (String, String) ]
conf =
  [
    ("", "CertiCoq -O0"), -- Baseline
    ("_cps", "CertiCoq -cps"),
    ("_opt", "CertiCoq -O1"),
    ("_opt_ll", "CertiCoq -O1 -lift-all")
    -- ("-caml", "ocamlc"),
    -- ("-camlopt", "ocamlopt")
  ]

-- Number of runs inside the same process
runs :: Double
runs = 10

-- Run a shell command and return the stdout
run_command :: String -> IO String
run_command command = do
  (stdin, Just hout, Just herr, procHandle) <- createProcess $ (shell command){ std_out = CreatePipe, std_err = CreatePipe }
  exitCode <- waitForProcess procHandle
  if exitCode == ExitSuccess
  then do
    stdOut <- System.IO.Strict.hGetContents hout;
    -- cleanupProcess (stdin, Just hout, Just herr, procHandle);
    return stdOut
  else do
    stdErr <- System.IO.Strict.hGetContents herr;
    -- cleanupProcess (stdin, Just hout, Just herr, procHandle);
    error $ concat [ show exitCode, command, stdErr ]


make_command :: String -- name of the test
             -> String -- compiler config
             -> String 
make_command test conf =
  let exec = if conf == "" then test else test ++ conf in
  "./" ++  exec ++ " | awk '/Time taken/ { print $5 }'"

run_test :: Int -- number of tests
         -> String -- test
         -> String -- config
         -> [ Double ] -- time for each test
         -> IO (Double, Double) -- (mean, standard error)
run_test 0 test config rs = do
  let tot = fromIntegral $ length rs
      mean = (sum rs) / tot
      std_err = sqrt ((sum (map (\i -> (i - mean) ** 2) rs)) / tot)
  return (mean, std_err)
run_test n test config rs = do
  let cmd = (make_command test config)
  out <- run_command cmd;
  -- printf "In cmd %s out is %s\n" cmd out;
  let r = read out :: Double
  run_test (n-1) test config ((r / runs):rs)

normalize :: [ (Double, Double) ] -> Double -> [ (Double, Double) ]
normalize res n = map (\(x, y) -> (x/n, y/n)) res

main :: IO ()
main = do
  args <- getArgs;
  let i = case args of
            [] -> 1 -- default number of iterations
            x : xs -> read x :: Int
  file <- openFile "TESTS" ReadMode
  contents <- System.IO.hGetContents file
  let tests =  words contents
  res <- sequence [ sequence [ run_test i t (fst c) [] | c <- conf ] | t <- tests ];
  printf "%20s" ""; sequence [ printf "%-20s" (snd c)  | c <- conf ]; printf "\n";
  sequence [ do
               printf "%-20s" t;
               let rs' = normalize rs (fst (head rs))
               sequence [ printf "%.3f +- %-11.3f" (fst r) (snd r) | r <- rs' ];
               printf "\n" | (rs, t) <- zip res tests ];
  hClose file
