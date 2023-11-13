package model.entities;

import java.util.Stack;

public class Tree {
    private Node root;
    private Integer size;

    public Tree() {
        this.size = 0;
    }

    public Tree(Node root) {
        this.root = root;
    }

    public Node getRoot() {
        return root;
    }

    public void setRoot(Node root) {
        this.root = root;
    }

    public void start(){
        insert(root, 5);
        insert(root, 3);
        insert(root, 8);
        insert(root, 9);
        insert(root, 1);
        insert(root, 10);
        insert(root, 7);
        insert(root, 25);
    }

    public Integer getSize() {
        return size;
    }

    public void setSize(Integer size) {
        this.size = size;
    }

    public void printPreOrder(Node root){
        System.out.print(root.getValue() + " ");

        if(root.getLeft() != null){
            printPreOrder(root.getLeft());
        }

        if(root.getRight() != null){
            printPreOrder(root.getRight());
        }
    }

    public void printInOrder(Node root){
        if(root.getLeft() != null){
            printInOrder(root.getLeft());
        }

        System.out.print(root.getValue() + " ");

        if(root.getRight() != null){
            printInOrder(root.getRight());
        }
    }

    public void printPostOrder(Node root){
        if(root.getLeft() != null){
            printPostOrder(root.getLeft());
        }

        if(root.getRight() != null){
            printPostOrder(root.getRight());
        }

        System.out.print(root.getValue() + " ");
    }

    public void setAllHeights(Node root){
        if(root.getLeft() != null){
            setAllHeights(root.getLeft());
        }

        if(root.getRight() != null){
            setAllHeights(root.getRight());
        }

        root.setHeight();
    }

    public String iterativePreOrder(Node node){
        Stack<Node> stack = new Stack<>();
        stack.push(node);

        StringBuilder result = new StringBuilder();

        while(!stack.empty()){
            Node aux = stack.pop();
            result.append(aux.getValue()).append(" ");

            if(aux.getRight() != null){
                stack.push(aux.getRight());
            }

            if(aux.getLeft() != null){
                stack.push(aux.getLeft());
            }
        }

        return result.toString();
    }

    public String iterativeInOrder(Node node){
        Stack<Node> stack = new Stack<>();
        Node currentNode = node;

        StringBuilder result = new StringBuilder();

        while(currentNode != null || !stack.isEmpty()){
            while(currentNode != null){
                stack.push(currentNode);
                currentNode = currentNode.getLeft();
            }

            currentNode = stack.pop();

            result.append(currentNode.getValue()).append(" ");

            currentNode = currentNode.getRight();
        }

        return result.toString();
    }

    public String iterativePostOrder(Node node){
        Stack<Node> stack = new Stack<>();
        stack.push(node);

        Stack<Integer> valuesList = new Stack<>();

        while(!stack.empty()){
            Node currentNode = stack.pop();
            valuesList.push(currentNode.getValue());

            if(currentNode.getLeft() != null){
                stack.push(currentNode.getLeft());
            }

            if(currentNode.getRight() != null){
                stack.push(currentNode.getRight());
            }
        }

        StringBuilder result = new StringBuilder();

        while (!valuesList.empty()){
            result.append(valuesList.pop()).append(" ");
        }

        return result.toString();
    }

    public boolean isThereANode(int value){
        return search(root, value) != null;
    }

    public Node search(Node root, int value){
        if(root == null || root.getValue() == value){
            return root;
        }

        if(root.getValue() < value){
            return search(root.getRight(), value);
        }

        return search(root.getLeft(), value);
    }

    public Node insert(Node root, int value){

        if (this.root == null){
            setRoot(new Node(value));

            return this.root;
        }

        int leftHeight = 0;
        int rightHeight = 0;

        if (root == null){
            root = new Node(value);
        }
        else if (value == root.getValue()){
            System.out.println("Elemento " + value + " já existe.");
            return root;
        }
        else if (value < root.getValue()){

            root.setLeft(insert(root.getLeft(), value));
            leftHeight = root.getLeft().getHeight();

            if (root.getRight() != null) {
                rightHeight = root.getRight().getHeight();
            }
        }
        else {
            root.setRight(insert(root.getRight(), value));
            rightHeight = root.getRight().getHeight();

            if (root.getLeft() != null) {
                leftHeight = root.getLeft().getHeight();
            }
        }

        root.setHeight(Math.max(rightHeight, leftHeight) + 1);

        return root;
    }

    public int getSize(Node root){
        return countNodes(root);
    }

    public int countNodes(Node root){
        if (root == null){
            return 0;
        }
        else {
             return  1 + (countNodes(root.getLeft()) + countNodes(root.getRight()));
        }

    }

    public double calculateMean(Node root){

        if (root == null){
            return 0;
        }

        Stack<Node> stack = new Stack<>();
        stack.push(root);

        int sumValues = 0;

        while(!stack.isEmpty()){
            Node aux = stack.pop();
            sumValues += aux.getValue();

            if(aux.getRight() != null){
                stack.push(aux.getRight());
            }

            if(aux.getLeft() != null){
                stack.push(aux.getLeft());
            }
        }

        int sizeTree = getSize(root);

        return (double) sumValues / sizeTree;

    }

}
