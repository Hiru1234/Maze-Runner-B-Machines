/* MazeRobot
 * Author: hsemb
 * Creation date: 25/12/2022
 */
MACHINE
    MazeRobot
SEES
    Maze
    
SETS
    MOVEMENTS = {Robot_cannot_move_north_due_to_maze_boundary, Robot_cannot_move_north_due_to_internal_maze_wall, Robot_successfully_moved_north, Robot_has_reached_exit_square, Robot_cannot_move_south_due_to_maze_boundary, Robot_cannot_move_south_due_to_internal_maze_wall, Robot_successfully_moved_south, Robot_cannot_move_east_due_to_maze_boundary, Robot_cannot_move_east_due_to_internal_maze_wall, Robot_successfully_moved_east, Robot_cannot_move_west_due_to_maze_boundary, Robot_cannot_move_west_due_to_internal_maze_wall, Robot_successfully_moved_west, Robot_cannot_teleport_out_of_the_maze, Robot_cannot_teleport_to_an_internal_wall_square, Robot_has_teleported_to_exit_square, Robot_successfully_teleported, Robot_has_returned_to_entrance_square};
    
    OUTPUT = {Yes, No}
    
DEFINITIONS
    isRobotHittingInternalWall(xAxis, yAxis) == (xAxis |-> yAxis : internalWall);
    isRobotInsideMaze(xAxis, yAxis) == (xAxis |-> yAxis : mazeSquares);
    hasRobotReachedExitSquare(xAxis, yAxis) == (xAxis |-> yAxis = exitSquare);
    increaseCoordinate(coordinate) == (coordinate + 1);
    decreaseCoordinate(coordinate) == (coordinate - 1);

     ANIMATION_FUNCTION == ({ row, col, img | col:xSquares & row: ySquares & img=0 & (col, 6-row) /: internalWall });
    
    ANIMATION_FUNCTION1 == ({ row, col, img | col: xSquares & row: ySquares  & img=1 & (col, 6-row) : internalWall });
    
    ANIMATION_FUNCTION2 == ({ row, col, img | col: xSquares & row: ySquares & img=2 & col=currentXPostion & row=(6-currentYPostion) });

    // Images for animations
    
    ANIMATION_IMG0 == "images/path.png";
    ANIMATION_IMG1 == "images/wall.png";
    ANIMATION_IMG2 == "images/robot.png";
    
VARIABLES
    currentXPostion,currentYPostion, robotRoute, visitedSquares
    
INVARIANT
    currentXPostion : xSquares &
    currentYPostion : ySquares &
    currentXPostion |-> currentYPostion : pathSquares &
    robotRoute : seq(pathSquares) &
    visitedSquares <: pathSquares
    
INITIALISATION
    currentXPostion := prj1( xSquares, ySquares )( entranceSquare ) ||
    currentYPostion := prj2( xSquares, ySquares )( entranceSquare ) ||
    robotRoute := [ entranceSquare ] ||
    visitedSquares := {}
    
OPERATIONS
    /*Moves robot one square up on the y plane */
    moveNorthOutcome <-- MoveNorth =
    PRE
        not(hasRobotReachedExitSquare(currentXPostion, currentYPostion))
    THEN
        IF
            isRobotInsideMaze(currentXPostion, increaseCoordinate(currentYPostion))
        THEN
            IF
                isRobotHittingInternalWall(currentXPostion, increaseCoordinate(currentYPostion))
            THEN
                moveNorthOutcome := Robot_cannot_move_north_due_to_internal_maze_wall 
            ELSE
                currentYPostion := increaseCoordinate(currentYPostion) ||
                robotRoute := robotRoute <- ( currentXPostion |-> increaseCoordinate(currentYPostion) ) ||
                visitedSquares := visitedSquares \/ {currentXPostion |-> currentYPostion} ||
                IF
                    hasRobotReachedExitSquare(currentXPostion, increaseCoordinate(currentYPostion))
                THEN
                    moveNorthOutcome := Robot_has_reached_exit_square 
                ELSE
                    moveNorthOutcome := Robot_successfully_moved_north 
                END              
            END
        ELSE
            moveNorthOutcome := Robot_cannot_move_north_due_to_maze_boundary
        END       
    END;
    
    /*Moves robot one square down on the y plane */
    moveSouthOutcome <-- MoveSouth =
    PRE
        not(hasRobotReachedExitSquare(currentXPostion, currentYPostion))
    THEN
        IF
            isRobotInsideMaze(currentXPostion, decreaseCoordinate(currentYPostion))
        THEN
            IF
                isRobotHittingInternalWall(currentXPostion, decreaseCoordinate(currentYPostion))
            THEN
                moveSouthOutcome := Robot_cannot_move_south_due_to_internal_maze_wall 
            ELSE
                currentYPostion := decreaseCoordinate(currentYPostion) ||
                robotRoute := robotRoute <- ( currentXPostion |-> decreaseCoordinate(currentYPostion) ) ||
                visitedSquares := visitedSquares \/ {currentXPostion |-> currentYPostion} ||
                IF
                    hasRobotReachedExitSquare(currentXPostion, decreaseCoordinate(currentYPostion))
                THEN
                    moveSouthOutcome := Robot_has_reached_exit_square 
                ELSE
                    moveSouthOutcome := Robot_successfully_moved_south 
                END              
            END
        ELSE
            moveSouthOutcome := Robot_cannot_move_south_due_to_maze_boundary
        END       
    END; 
     
    /*Moves robot by one square to the right on the x plane */
    moveEastOutcome <-- MoveEast =
    PRE
        not(hasRobotReachedExitSquare(currentXPostion, currentYPostion))
    THEN
        IF
            isRobotInsideMaze(increaseCoordinate(currentXPostion), currentYPostion)
        THEN
            IF
                isRobotHittingInternalWall(increaseCoordinate(currentXPostion), currentYPostion)
            THEN
                moveEastOutcome := Robot_cannot_move_east_due_to_internal_maze_wall 
            ELSE
                currentXPostion := increaseCoordinate(currentXPostion) ||
                robotRoute := robotRoute <- ( increaseCoordinate(currentXPostion) |-> currentYPostion ) ||
                visitedSquares := visitedSquares \/ {currentXPostion |-> currentYPostion} ||
                IF
                    hasRobotReachedExitSquare(increaseCoordinate(currentXPostion), currentYPostion)
                THEN
                    moveEastOutcome := Robot_has_reached_exit_square 
                ELSE
                    moveEastOutcome := Robot_successfully_moved_east 
                END              
            END
        ELSE
            moveEastOutcome := Robot_cannot_move_east_due_to_maze_boundary
        END       
    END;
    
    /*Moves robot by one square to the left on the x plane */
    moveWestOutcome <-- MoveWest =
    PRE
        not(hasRobotReachedExitSquare(currentXPostion, currentYPostion))
    THEN
        IF
            isRobotInsideMaze(decreaseCoordinate(currentXPostion), currentYPostion)
        THEN
            IF
                isRobotHittingInternalWall(decreaseCoordinate(currentXPostion), currentYPostion)
            THEN
                moveWestOutcome := Robot_cannot_move_west_due_to_internal_maze_wall 
            ELSE
                currentXPostion := decreaseCoordinate(currentXPostion) ||
                robotRoute := robotRoute <- ( decreaseCoordinate(currentXPostion) |-> currentYPostion ) ||
                visitedSquares := visitedSquares \/ {currentXPostion |-> currentYPostion} ||
                IF
                    hasRobotReachedExitSquare(decreaseCoordinate(currentXPostion), currentYPostion)
                THEN
                    moveWestOutcome := Robot_has_reached_exit_square 
                ELSE
                    moveWestOutcome := Robot_successfully_moved_west 
                END              
            END
        ELSE
            moveWestOutcome := Robot_cannot_move_west_due_to_maze_boundary
        END       
    END;
    
    /*Teleports the robot to any given path square in maze*/
    teleportOutcome <-- Teleport(GoToX, GoToY) =
    PRE
        not(hasRobotReachedExitSquare(currentXPostion, currentYPostion)) &
        GoToX : 1..7 & GoToX /= currentXPostion &
        GoToY : 1..5 & GoToY /= currentYPostion
    THEN
        IF
            isRobotInsideMaze(GoToX, GoToY)
        THEN
            IF
                isRobotHittingInternalWall(GoToX, GoToY)
            THEN
                teleportOutcome := Robot_cannot_teleport_to_an_internal_wall_square
            ELSE
                currentXPostion := GoToX ||
                currentYPostion := GoToY ||
                robotRoute := robotRoute <- ( GoToX |-> GoToY ) ||
                visitedSquares := visitedSquares \/ {currentXPostion |-> currentYPostion} ||
                IF
                    hasRobotReachedExitSquare(GoToX, GoToY)
                THEN
                    teleportOutcome := Robot_has_teleported_to_exit_square 
                ELSE
                    teleportOutcome := Robot_successfully_teleported 
                END              
            END
        ELSE
            teleportOutcome := Robot_cannot_teleport_out_of_the_maze
        END
    END;
    
    /*Outputs the current position of the robot in the maze*/
    currentPosition <-- GetPosition=
    BEGIN
        currentPosition := currentXPostion |-> currentYPostion
    END;
    
    /*Outputs whether the robot is on the exit square or not*/    
    isRobotOnExit <-- FoundExit=
    BEGIN
        IF hasRobotReachedExitSquare(currentXPostion, currentYPostion)
        THEN
            isRobotOnExit := Yes
        ELSE
            isRobotOnExit := No
        END
    END;
    
    /*Outputs whether the robot has visited a maze square or not (outputs yes only if robot has visited and moved away from the square)*/
    isSquareVisited <-- HasVisitedSquare(squareCoordinates)=
    PRE
        squareCoordinates : pathSquares
    THEN
        IF
            squareCoordinates : visitedSquares & squareCoordinates /= (currentXPostion |-> currentYPostion)
        THEN
            isSquareVisited := Yes
        ELSE
            isSquareVisited := No
        END
    END;
    
    /*Outputs the sequence of squares the Robot has visited in the maze*/
    robotRouteOutcome <-- RobotsRoute =
    BEGIN
        robotRouteOutcome := robotRoute
    END;
    
    /*Returns the robot to entrance square*/
    resetOutcome <-- Reset=
    BEGIN
        currentXPostion := prj1( xSquares, ySquares )( entranceSquare ) ||
        currentYPostion := prj2( xSquares, ySquares )( entranceSquare ) ||
        robotRoute := [ entranceSquare ] ||
        visitedSquares := {} ||
        resetOutcome := Robot_has_returned_to_entrance_square
    END
END
