import java.util.HashSet;
import java.util.Objects;
import java.util.Set;

class VariableState{

    Set<ProgramPoint.Instruction> definitionPoints = new HashSet<>();
    String pointsTo = null;
    String type = null;


    public void setPointsTo(String pointsTo) {
        this.pointsTo = pointsTo;
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
        return this.definitionPoints;
    }

    public String getPointsTo() {
        return pointsTo;
    }

    @Override
    public VariableState clone() {
        VariableState newState = new VariableState();
        newState.pointsTo = this.pointsTo;
        newState.type = this.type;
        newState.definitionPoints = new HashSet<>(this.definitionPoints);
        return newState;
    }

    public VariableState copyNew(VariableState def) {
        VariableState newState = new VariableState();
        newState.definitionPoints = def.definitionPoints;
        newState.pointsTo = this.pointsTo;
        newState.type = this.type;
        return newState;
    }


    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null || getClass() != obj.getClass()) return false;
        VariableState other = (VariableState) obj;
        return  Objects.equals(definitionPoints, other.definitionPoints) &&
                Objects.equals(pointsTo, other.pointsTo) &&
                type == other.type;
    }

    public VariableState join(VariableState other) {
        VariableState result = this.clone();

        result.addAllDefinitionPoint(other.getDefinitionPoints());

        return result;
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

