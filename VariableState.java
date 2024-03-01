import java.util.HashSet;
import java.util.Objects;
import java.util.Set;

class VariableState{

    Set<ProgramPoint.Instruction> definitionPoints = new HashSet<>();
    boolean isTop = false;
    String pointsTo = null;
    boolean isHeap=false;
    String type = null;

    void markAsTop() {
        if(this.pointsTo == null){
            this.isTop = true;
        }
    }


    public void setPointsTo(String pointsTo) {
        this.pointsTo = pointsTo;
        isTop = false;
    }

    public String getType() {
        return this.type;
    }

    public void setDefinitionPoint(ProgramPoint.Instruction instruction) {
        Set<ProgramPoint.Instruction> newlist = new HashSet<>();
        newlist.add(instruction);
        this.definitionPoints = newlist;
    }

    public void addDefinitionPoint(ProgramPoint.Instruction instruction) {
        this.definitionPoints.add(instruction);
    }

    public void addAllDefinitionPoint(Set<ProgramPoint.Instruction> instructions) {
        for (ProgramPoint.Instruction instruction : instructions) {
            this.definitionPoints.add(instruction);
        }
    }

    // Getter for definitionPoints
    public Set<ProgramPoint.Instruction> getDefinitionPoints() {
        return definitionPoints;
    }

    public String getPointsTo() {
        return pointsTo;
    }

    public void merge(VariableState predecessorState) {
        this.join(predecessorState);
    }

    @Override
    public VariableState clone() {
        VariableState newState = new VariableState();
        newState.isTop = this.isTop;
        newState.pointsTo = this.pointsTo;
        newState.type = this.type;
        newState.definitionPoints = new HashSet<>(this.definitionPoints);
        return newState;
    }

    public VariableState copyNew(VariableState def) {
        VariableState newState = new VariableState();
        newState.definitionPoints = def.definitionPoints;
        newState.isTop = this.isTop;
        newState.pointsTo = this.pointsTo;
        newState.type = this.type;
        return newState;
    }


    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        VariableState other = (VariableState) obj;
        return isTop == other.isTop &&
                Objects.equals(definitionPoints, other.definitionPoints) &&
                Objects.equals(pointsTo, other.pointsTo) &&
                type == other.type;
    }

    void weakUpdate(VariableState other) {
        if (this.isTop || other.isTop) {
            this.markAsTop();
        } else if (this.pointsTo != null && other.pointsTo != null && !Objects.equals(this.pointsTo, other.pointsTo)) {
            this.markAsTop();
        }
    }

    public VariableState join(VariableState other) {
        VariableState result = this.clone();

        //should change after worklist
        if (this.isTop || other.isTop) {
            result.markAsTop();
        }else{
            result.markAsTop();
        }

        return result;
    }

    public boolean isHeap() {
        return isHeap;
    }

    public void setHeap(boolean heap) {
        isHeap = heap;
    }

    public void setType(String type) {
        this.type = type;
    }

    @Override
    public String toString() {
        return "definitionPoints=" + definitionPoints +
                ", pointsTo:'" + pointsTo + '\'' +
                ", type:'" + type + '\'';
    }
}

