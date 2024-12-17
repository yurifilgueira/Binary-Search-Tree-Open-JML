package model.entities;

public class Node {
    //@ spec_public
    private int value;
    //@ spec_public
    /*@ nullable */
    private Node left;
    //@ spec_public
    /*@ nullable */
    private Node right;
    //@ spec_public
    private int depth;
    //@ spec_public
    private int height;

    //@ public invariant height >= 0;
    //@ public invariant depth >= 0;

    //@ public normal_behavior
    //@ ensures Integer.MIN_VALUE <= value <= Integer.MAX_VALUE;
    //@ ensures left == null;
    //@ ensures right == null;
    //@ pure
    public Node(int value) {
        this.value = value;
        left = null;
        right = null;
    }

    //@ public normal_behavior
    //@ pure
    public int getValue() {
        return value;
    }

    //@ public normal_behavior
    //@ requires Integer.MIN_VALUE <= value <= Integer.MAX_VALUE;
    //@ ensures this.value == value;
    //@ assignable this.value;
    public void setValue(int value) {
        this.value = value;
    }

    //@ public normal_behavior
    //@ pure
    /*@ nullable*/
    public Node getLeft() {
        return left;
    }

    //@ public normal_behavior
    //@ ensures this.left == left;
    //@ assignable this.left;
    public void setLeft(/*@ nullable */ Node left) {
        this.left = left;
    }

    //@ public normal_behavior
    //@ pure
    /*@ nullable*/
    public Node getRight() {
        return right;
    }

    //@ public normal_behavior
    //@ ensures this.right == right;
    //@ assignable this.right;
    public void setRight(/*@ non_null */ Node right) {
        this.right = right;
    }

    //@ public normal_behavior
    //@ ensures \result >= 0;
    //@ pure
    public int getDepth() {
        return depth;
    }

    //@ public normal_behavior
    //@ requires 0 <= depth <= Integer.MAX_VALUE;
    //@ ensures this.depth == depth;
    //@ assignable this.depth;
    public void setDepth(int depth) {
        this.depth = depth;
    }

    //@ public normal_behavior
    //@ ensures \result >= 0;
    //@ pure
    public int getHeight() {
        return height;
    }

    //@ requires height >= 0;
    //@ ensures this.height == height;
    //@ assignable this.height;
    public void setHeight(int height) {
        this.height = height;
    }

    //@ assignable height;
    public void setHeight(){
        int alt1, alt2;

        if(left != null){
            alt1 = left.getHeight();
        }else{
            alt1 = 0;
        }

        if(right != null){
            alt2 = right.getHeight();
        }else{
            alt2 = 0;
        }

        //@ assert alt1 >= 0 && alt2 >= 0;

        //@ assume alt1 + 1 <= Integer.MAX_VALUE;
        //@ assume alt2 + 1 <= Integer.MAX_VALUE;
        if(alt1 > alt2){
            height = alt1 + 1;
        }else{
            height = alt2 + 1;
        }

        //@ assert height == (alt1 + 1) || height == (alt2 + 1);
        //@ assert (alt1 + 1 <= Integer.MAX_VALUE) && (alt2 + 1 <= Integer.MAX_VALUE);
    }

}
