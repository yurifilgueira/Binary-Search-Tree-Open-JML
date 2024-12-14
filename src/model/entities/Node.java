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

    //@ pure
    public int getValue() {
        return value;
    }

    //@ ensures this.value == value;
    //@ assignable this.value;
    public void setValue(int value) {
        this.value = value;
    }

    //@ pure
    /*@ nullable*/
    public Node getLeft() {
        return left;
    }

    //@ ensures this.left == left;
    //@ assignable this.left;
    public void setLeft(/*@ nullable */ Node left) {
        this.left = left;
    }

    //@ pure
    /*@ nullable*/
    public Node getRight() {
        return right;
    }

    //@ ensures this.right == right;
    //@ assignable this.right;
    public void setRight(/*@ non_null */ Node right) {
        this.right = right;
    }

    //@ pure
    public int getDepth() {
        return depth;
    }

    //@ requires depth >= 0;
    //@ ensures this.depth == depth;
    //@ assignable this.depth;
    public void setDepth(int depth) {
        this.depth = depth;
    }

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

        //@ assume alt1 >= 0 && alt2 >= 0;
        //@ assume 0 < alt1 + 1 <= Integer.MAX_VALUE;
        //@ assume 0 < alt2 + 1 <= Integer.MAX_VALUE;
        if(alt1 > alt2){
            height = alt1 + 1;
        }else{
            height = alt2 + 1;
        }

        assert height == (alt1 + 1) || height == (alt2 + 1);
    }

}
