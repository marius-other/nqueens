import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.DimacsReader;
import org.sat4j.reader.Reader;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;

/**
 * NQueensProblem transforms the n-queens problem into a SAT problem.
 * A variable in the SAT problem is true iff a queen is in the corresponding position on the chessboard.
 * The SAT solver we use, sat4j, expects a file in the Dimacs CNF format.
 * Presumably there are better ways to load the SAT instance into the sat4j solver but this will do for now.
 */
public class NQueensProblem {

    final public static int REASONABLE_INSTANCE_UPPER_BOUND = 1000;
    final public static int REASONABLE_TIMEOUT = 600;

    public static void main(String[] args) throws Exception {
        if (args.length != 1) {
            throw new IllegalArgumentException(String.format("Expected 1 argument instead of %d.", args.length));
        }
        final int nQueens = Integer.parseInt(args[0]);
        if (nQueens <= 0 || nQueens > REASONABLE_INSTANCE_UPPER_BOUND) {
            throw new NumberFormatException(
                    String.format("Expected integer in range [0, %d] instead of %d.", REASONABLE_INSTANCE_UPPER_BOUND, nQueens));
        }

        IProblem satProblem;
        NQueensProblem nQueensProblem = new NQueensProblem(nQueens);
        nQueensProblem.setAllSatClauses();
        ISolver solver = SolverFactory.newDefault();
        solver.setTimeout(REASONABLE_TIMEOUT);
        Reader reader = new DimacsReader(solver);
        try (ByteArrayOutputStream baos = new ByteArrayOutputStream()) {
            try (PrintStream printStream = new PrintStream(baos)) {
                nQueensProblem.printAsDimacsCnf(printStream);
            }
            try (ByteArrayInputStream inputStream = new ByteArrayInputStream(baos.toByteArray())) {
                satProblem = reader.parseInstance(inputStream);
            }
        }

        boolean solution[] = new boolean[nQueens * nQueens];
        if (satProblem.isSatisfiable()) {
            for (int v : satProblem.model()) {
                if (v > 0) {
                    solution[v - 1] = true;
                }
            }
        }
        for (int line = 0; line < nQueens; line++) {
            for (int column = 0; column < nQueens; column++) {
                System.out.print(solution[line * nQueens + column] ? 'Q' : '.');
            }
            System.out.println();
        }
    }

    public NQueensProblem(int nQueens) {
        this.nQueens = nQueens;
        this.nVariables = nQueens * nQueens;
        this.maxStep = (nQueens - 1) / 2;
    }

    final private int nQueens;
    final private int nVariables;
    final private int maxStep;
    private ArrayList<String> clauses = new ArrayList<>();

    private void setAllSatClauses() {
        // basic n-queens rules
        for (int i = 0; i < nQueens; i++) {
            // line rule
            exactlyOneTrue(walk(i, 0, 0, 1));
            // column rule
            exactlyOneTrue(walk(0, i, 1, 0));
            // diagonal rules
            atMostOneTrue(walk(i, 0, -1, 1));
            atMostOneTrue(walk(i, 0, -1, 1));
            atMostOneTrue(walk(0, i, 1, -1));
            atMostOneTrue(walk(0, i, 1, 1));
        }
        // break horizontal symmetry
        exactlyOneTrue(walk(0, nQueens / 2, 0, 1));
        // break vertical symmetry
        for (int i = nQueens / 2; i < nQueens; i++) {
            for (int j = 0; j < i; j++) {
                notAllTrue(i * nQueens, (j + 1) * nQueens - 1);
            }
        }
        // two queens maximum per line
        for (int line = 0; line < nQueens; line++) {
            for (int column = 0; column < nQueens; column++) {
                twoQueensMaxPerLine(line, column);
            }
        }
    }

    private int[] walk(int line, int column, int lineStep, int columnStep) {
        int[] variables = new int[nQueens];
        int nSteps = 0;
        while (nSteps < nQueens && isValid(line, column)) {
            variables[nSteps++] = line * nQueens + column;;
            line += lineStep;
            column += columnStep;
        }
        return Arrays.copyOf(variables, nSteps);
    }

    private boolean isValid(int lineOrcolumn) {
        return (lineOrcolumn >= 0 && lineOrcolumn < nQueens);
    }

    private boolean isValid(int line, int column) {
        return isValid(line) && isValid(column);
    }

    private void twoQueensMaxPerLine(int line, int column) {
        int v0 = line * nQueens + column; // origin point for line
        for (int lineStep = -maxStep; lineStep <= maxStep; lineStep++) {
            int line1 = line + lineStep;
            if (lineStep != 0 && isValid(line1 + lineStep)) {
                for (int columnStep = lineStep; columnStep <= maxStep; columnStep++) {
                    int column1 = column + columnStep;
                    if (columnStep != 0 && isValid(column1 + columnStep)) {
                        int v1 = line1 * nQueens + column1; // nearest point to origin on line in chosen direction
                        for (int line2 = line1 + lineStep, column2 = column1 + columnStep;
                             isValid(line2, column2);
                             line2 += lineStep, column2 += columnStep) {
                            int v2 = line2 * nQueens + column2;
                            notAllTrue(v0, v1, v2);
                        }
                    }
                }
            }
        }
    }

    private void exactlyOneTrue(int... variables) {
        atLeastOneTrue(variables);
        atMostOneTrue(variables);
    }

    private void atMostOneTrue(int... variables) {
        for (int i = 0; i < variables.length - 1; i++) {
            for (int j = i + 1; j < variables.length; j++) {
                notAllTrue(variables[i], variables[j]);
            }
        }
    }

    private void atLeastOneTrue(int... atLeastOneMustBeTrue) {
        if (atLeastOneMustBeTrue.length > 0) {
            addDisjunctiveClause(atLeastOneMustBeTrue, new int[0]);
        }
    }

    private void notAllTrue(int... atLeastOneMustBeFalse) {
        addDisjunctiveClause(new int[0], atLeastOneMustBeFalse);
    }

    private void addDisjunctiveClause(int[] trueVariables, int[] falseVariables) {
        StringBuilder sb = new StringBuilder();
        for (int trueVariable : trueVariables) {
            sb.append(trueVariable + 1).append(' ');
        }
        for (int falseVariable : falseVariables) {
            sb.append(-(falseVariable + 1)).append(' ');
        }
        String clause = sb.append('0').toString();
        clauses.add(clause);
    }

    public void printAsDimacsCnf(PrintStream printStream) {
        printStream.println(String.format("c %d queens problem (variant)", nQueens));
        printStream.println(String.format("p cnf %d %d", nVariables, clauses.size()));
        clauses.forEach(printStream::println);
    }
}
