package solver;

import java.util.*;

public class SokoBot {

    public String solveSokobanPuzzle(int width, int height, char[][] mapData, char[][] itemsData) {
        int playerRow = -1, playerCol = -1;
        for (int r = 0; r < height; r++) {
            for (int c = 0; c < width; c++) {
                if (itemsData[r][c] == '@') {
                    playerRow = r;
                    playerCol = c;
                }
            }
        }
        PuzzleSolver solver = new PuzzleSolver(width, height, mapData);
        return solver.solve(playerRow, playerCol, itemsData);
    }
}

class PuzzleSolver {

    private final int width, height;
    private final boolean[][] wall;
    private final boolean[][] target;
    private final int totalTargets;
    private final List<int[]> targetList;
    private static final long TIME_LIMIT_MS = 13_500;
    private long startTime;
    private DeadlockDetector deadlockDetector;
    private final boolean[][] deadTiles; // added

    public PuzzleSolver(int width, int height, char[][] mapData) {
        this.width = width;
        this.height = height;
        this.wall = new boolean[height][width];
        this.target = new boolean[height][width];
        this.targetList = new ArrayList<>();
        this.deadTiles = new boolean[height][width]; // added

        for (int r = 0; r < height; r++) {
            for (int c = 0; c < width; c++) {
                char ch = mapData[r][c];
                if (ch == '#') {
                    wall[r][c] = true;
                } else if (ch == '.') {
                    target[r][c] = true;
                    targetList.add(new int[]{r, c});
                }
            }
        }
        this.totalTargets = targetList.size();
        this.deadlockDetector = new DeadlockDetector(wall, target, width, height);
        precomputeDeadTiles(); // added
    }

    private int encode(int r, int c) {
        return r * width + c;
    }

    private int decodeRow(int pos) { return pos / width; }
    private int decodeCol(int pos) { return pos % width; }

    private void precomputeDeadTiles() { // added method
        for (int r = 0; r < height; r++) {
            for (int c = 0; c < width; c++) {
                if (wall[r][c] || target[r][c]) continue;

                if (isWall(r - 1, c) || isWall(r + 1, c)) {
                    if (isDeadEnd(r, c, 0, -1) && isDeadEnd(r, c, 0, 1)) {
                        deadTiles[r][c] = true;
                    }
                }

                if (isWall(r, c - 1) || isWall(r, c + 1)) {
                    if (isDeadEnd(r, c, -1, 0) && isDeadEnd(r, c, 1, 0)) {
                        deadTiles[r][c] = true;
                    }
                }
            }
        }
    }

    private boolean isDeadEnd(int r, int c, int dr, int dc) {
        int currR = r + dr;
        int currC = c + dc;
        while (!isWall(currR, currC)) {
            if (target[currR][currC]) return false; 
            
            if (dr == 0 && !isWall(currR - 1, currC) && !isWall(currR + 1, currC)) return false; 
            if (dc == 0 && !isWall(currR, currC - 1) && !isWall(currR, currC + 1)) return false;
            
            currR += dr;
            currC += dc;
        }
        return true; 
    }
    
    public String solve(int playerRow, int playerCol, char[][] itemsData) {
        startTime = System.currentTimeMillis();

        List<Integer> crateList = new ArrayList<>();
        for (int r = 0; r < height; r++) {
            for (int c = 0; c < width; c++) {
                if (itemsData[r][c] == '$') {
                    crateList.add(encode(r, c));
                }
            }
        }
        int[] crates = toSortedArray(crateList);
        int player = encode(playerRow, playerCol);

        State start = new State(player, crates, null, '\0', 0, heuristic(player, crates));
        PriorityQueue<State> openSet = new PriorityQueue<>(Comparator.comparingInt(State::fCost));
        HashSet<State> visited = new HashSet<>();

        openSet.add(start);
        State bestFallback = start;

        while (!openSet.isEmpty()) {
            if (System.currentTimeMillis() - startTime > TIME_LIMIT_MS) {
                return bestFallback.reconstructPath();
            }

            State current = openSet.poll();

            if (visited.contains(current)) {
                continue;
            }
            visited.add(current);

            if (current.hCost < bestFallback.hCost) {
                bestFallback = current;
            }

            if (isGoal(current.crates)) {
                return current.reconstructPath();
            }

            for (Direction dir : Direction.values()) {
                expandMove(current, dir, openSet, visited);
            }
        }

        return bestFallback.reconstructPath();
    }

    private enum Direction {
        UP(-1, 0, 'u'),
        DOWN(1, 0, 'd'),
        LEFT(0, -1, 'l'),
        RIGHT(0, 1, 'r');

        final int dr, dc;
        final char moveChar;

        Direction(int dr, int dc, char moveChar) {
            this.dr = dr;
            this.dc = dc;
            this.moveChar = moveChar;
        }
    }

    private void expandMove(State current, Direction dir, PriorityQueue<State> openSet, HashSet<State> visited) {
        int dr = dir.dr;
        int dc = dir.dc;
        char moveChar = dir.moveChar;

        int pr = decodeRow(current.playerPos);
        int pc = decodeCol(current.playerPos);
        int nr = pr + dr;
        int nc = pc + dc;

        if (isWall(nr, nc)) {
            return;
        }

        int newPlayerPos = encode(nr, nc);
        int[] newCrates = current.crates;

        int crateIndex = indexOfCrate(current.crates, newPlayerPos);
        if (crateIndex >= 0) {
            int crateNewRow = nr + dr;
            int crateNewCol = nc + dc;

            if (isWall(crateNewRow, crateNewCol)) {
                return;
            }
            
            if (deadTiles[crateNewRow][crateNewCol]) { // added
                return;
            }

            int crateNewPos = encode(crateNewRow, crateNewCol);

            if (indexOfCrate(current.crates, crateNewPos) >= 0) {
                return;
            }

            newCrates = current.crates.clone();
            newCrates[crateIndex] = crateNewPos;
            Arrays.sort(newCrates);

            if (deadlockDetector.isCornerDeadlock(crateNewRow, crateNewCol)) {
                return;
            }
        }

        State next = new State(
            newPlayerPos,
            newCrates,
            current,
            moveChar,
            current.gCost + 1,
            heuristic(newPlayerPos, newCrates)
        );

        if (!visited.contains(next)) {
            openSet.add(next);
        }
    }

    private int heuristic(int playerPos, int[] crates) {
        int totalCrateDistance = 0;
        int nearestUnplacedCrateDist = Integer.MAX_VALUE;

        int pr = decodeRow(playerPos);
        int pc = decodeCol(playerPos);

        for (int cratePos : crates) {
            int cr = decodeRow(cratePos);
            int cc = decodeCol(cratePos);

            int best = Integer.MAX_VALUE;
            for (int[] t : targetList) {
                int dist = Math.abs(cr - t[0]) + Math.abs(cc - t[1]);
                if (dist < best) best = dist;
            }
            totalCrateDistance += best;

            if (best > 0) {
                int playerToCrate = Math.abs(pr - cr) + Math.abs(pc - cc);
                nearestUnplacedCrateDist = Math.min(nearestUnplacedCrateDist, playerToCrate);
            }
        }

        if (nearestUnplacedCrateDist == Integer.MAX_VALUE) nearestUnplacedCrateDist = 0;

        return totalCrateDistance + nearestUnplacedCrateDist;
    }

    private boolean isGoal(int[] crates) {
        for (int cratePos : crates) {
            if (!target[decodeRow(cratePos)][decodeCol(cratePos)]) return false;
        }
        return true;
    }

    private boolean isWall(int r, int c) {
        if (r < 0 || r >= height || c < 0 || c >= width) return true;
        return wall[r][c];
    }

    private int indexOfCrate(int[] crates, int pos) {
        return Arrays.binarySearch(crates, pos);
    }

    private int[] toSortedArray(List<Integer> list) {
        int[] arr = new int[list.size()];
        for (int i = 0; i < arr.length; i++) arr[i] = list.get(i);
        Arrays.sort(arr);
        return arr;
    }
}

class DeadlockDetector {

    private final boolean[][] wall;
    private final boolean[][] target;
    private final int width, height;

    public DeadlockDetector(boolean[][] wall, boolean[][] target, int width, int height) {
        this.wall = wall;
        this.target = target;
        this.width = width;
        this.height = height;
    }

    public boolean isCornerDeadlock(int crateRow, int crateCol) {
        if (target[crateRow][crateCol]) {
            return false;
        }

        boolean wallUp    = isWall(crateRow - 1, crateCol);
        boolean wallDown  = isWall(crateRow + 1, crateCol);
        boolean wallLeft  = isWall(crateRow, crateCol - 1);
        boolean wallRight = isWall(crateRow, crateCol + 1);

        return (wallUp && wallLeft) || (wallUp && wallRight)
            || (wallDown && wallLeft) || (wallDown && wallRight);
    }

    private boolean isWall(int r, int c) {
        if (r < 0 || r >= height || c < 0 || c >= width) return true;
        return wall[r][c];
    }
}

class State {

    public final int playerPos;
    public final int[] crates;
    public final State parent;
    public final char moveTaken;
    public final int gCost;
    public final int hCost;

    public State(int playerPos, int[] crates, State parent, char moveTaken, int gCost, int hCost) {
        this.playerPos = playerPos;
        this.crates = crates;
        this.parent = parent;
        this.moveTaken = moveTaken;
        this.gCost = gCost;
        this.hCost = hCost;
    }

    public int fCost() {
        return gCost + hCost;
    }

    public String reconstructPath() {
        StringBuilder sb = new StringBuilder();
        State cur = this;
        while (cur.parent != null) {
            sb.append(cur.moveTaken);
            cur = cur.parent;
        }
        return sb.reverse().toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (!(o instanceof State)) return false;
        State other = (State) o;
        return playerPos == other.playerPos && Arrays.equals(crates, other.crates);
    }

    @Override
    public int hashCode() {
        int result = playerPos;
        result = 31 * result + Arrays.hashCode(crates);
        return result;
    } 
} 
