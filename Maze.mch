/* Maze
 * Author: hsemb
 * Creation date: 28/12/2022
 */
MACHINE
    Maze
    
CONSTANTS
    xSquares, ySquares, mazeSquares, pathSquares, internalWall, entranceSquare, exitSquare
    
PROPERTIES
    xSquares = 1..7 &
    ySquares = 1..5 &
    mazeSquares = xSquares * ySquares &
    
    internalWall <: mazeSquares &
    internalWall = {1 |-> 3 , 2 |-> 1 , 2 |-> 3 , 2 |->5 , 3 |-> 3 , 4 |-> 2 , 4 |-> 3 , 4 |-> 4 , 6 |-> 1 , 
        6 |-> 2 , 6 |-> 4 , 7 |-> 4} &
    
    pathSquares <: mazeSquares &
    pathSquares /\ internalWall = {} &
    pathSquares \/ internalWall = mazeSquares &
    
    entranceSquare : pathSquares & entranceSquare = 1 |-> 1 &
    exitSquare : pathSquares & exitSquare = 1 |-> 5

END
