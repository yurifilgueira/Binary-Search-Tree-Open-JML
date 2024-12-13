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

    public Node(int value) {
        this.value = value;
        left = null;
        right = null;
    }

    //@ pure
    public int getValue() {
        return value;
    }

    public void setValue(int value) {
        this.value = value;
    }

    //@ pure
    /*@ nullable*/
    public Node getLeft() {
        return left;
    }

    public void setLeft(/*@ nullable */ Node left) {
        this.left = left;
    }

    //@ pure
    /*@ nullable*/
    public Node getRight() {
        return right;
    }

    public void setRight(/*@ non_null */ Node right) {
        this.right = right;
    }

    //@ pure
    public int getDepth() {
        return depth;
    }

    public void setDepth(int depth) {
        this.depth = depth;
    }

    //@ pure
    public int getHeight() {
        return height;
    }

    public void setHeight(int height) {
        this.height = height;
    }

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
    }

}
