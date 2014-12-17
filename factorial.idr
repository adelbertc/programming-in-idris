module Main
%flag C "-O3"

factorial : Int -> Int
factorial 0 = 1
factorial n = n * (factorial (n - 1))

main : IO ()
main = do
  putStrLn $ show $ factorial 3
