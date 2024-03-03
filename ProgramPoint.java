import java.util.ArrayList;
import java.util.List;

public class ProgramPoint {

    public interface Instruction extends Comparable<Instruction> {
        List<Instruction> getSuccessors();
        void addSuccessor(Instruction successor);
        String getBb();
        String getName();
        String getInstructure();
    }

    public static class NonTermInstruction implements Instruction {
        private String bb;
        private int index = 0;
        private String instructure = null;

        private List<Instruction> successors = new ArrayList<>();

        public NonTermInstruction(String bb, int i, String instructure) {
            this.bb = bb;
            this.index = i;
            this.instructure= instructure;
        }

        @Override
        public int compareTo(Instruction other) {
            int bbCompare = this.getBb().compareTo(other.getBb());
            if (bbCompare != 0) {
                return bbCompare;
            }

            if(other instanceof Terminal) {
                return -1;
            }

            if (other instanceof NonTermInstruction) {
                NonTermInstruction nonTermOther = (NonTermInstruction) other;
                Integer res = Integer.compare(this.index, nonTermOther.index);
                return res;
            }
            return 0;
        }

        @Override
        public List<Instruction> getSuccessors() {
            return successors;
        }

        @Override
        public void addSuccessor(Instruction successor) {
            this.successors.add(successor);
        }

        public String getBb() {
            return bb;
        }

        public String getName(){
            return bb + "." + index;
        }

        public void setBb(String bb) {
            this.bb = bb;
        }

        public int getIndex() {
            return index;
        }

        public void setIndex(int index) {
            this.index = index;
        }

        public String getInstructure() {
            return instructure;
        }

        public void setInstructure(String instructure) {
            this.instructure = instructure;
        }

        @Override
        public String toString() {
            return bb + "." + index;
        }
    }

    public static class Terminal implements Instruction {
        private String bb;

        private String instructure = null;

        private List<Instruction> successors = new ArrayList<>();

        public Terminal(String bb, String instructure) {
            this.bb = bb;
            this.instructure = instructure;
        }

        @Override
        public List<Instruction> getSuccessors() {
            return successors;
        }

        @Override
        public void addSuccessor(Instruction successor) {
            this.successors.add(successor);
        }

        @Override
        public int compareTo(Instruction other) {
            int bbCompare = this.getBb().compareTo(other.getBb());
            if (bbCompare != 0) {
                return bbCompare;
            }

            if (other instanceof NonTermInstruction) {
                return 1;
            }

            return 0;
        }


        public String getBb() {
            return bb;
        }

        public String getName(){
            return bb + ".term";
        }

        public void setBb(String bb) {
            this.bb = bb;
        }

        public String getInstructure() {
            return instructure;
        }

        public void setInstructure(String instructure) {
            this.instructure = instructure;
        }

        @Override
        public String toString() {
            return bb + ".term" ;
        }
    }
}
