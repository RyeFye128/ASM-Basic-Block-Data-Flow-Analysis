/*
 * Author: Ryan Chartier
 * Feb 14, 2017
 * CS 581
 */
import java.io.FileInputStream;
import java.io.StringWriter;
import java.io.PrintWriter;
import java.util.LinkedList;
import java.util.List;
import org.objectweb.asm.*;
import org.objectweb.asm.tree.*;
import org.objectweb.asm.util.*;

//class that records block successor(s)
class BlockHeader
{
	private LinkedList<Integer> succ;
	private int blockNum;
	
	public BlockHeader(int blockNum)
	{
		this.blockNum = blockNum;
		succ = new LinkedList<Integer>();
		
	}
	public boolean isEmpty()
	{
		return(succ.size() == 0);
	}
	public void addSucc(int succBlock)
	{
		succ.add(succBlock);
	}
	public int getBlockNum()
	{
		return blockNum;
	}
	public int edgeSize()
	{
		return succ.size();
	}

	/*
	 * Formats the block successors into what the assignment asks for (succ: x, y, z...)
	 */
	public void print()
	{
		String input = "";
		for(int i = 0; i < succ.size(); i++)
		{
			if( i == 0)
			{
				input = "" + succ.get(i);
			}
			else
			{
				input += ", " + succ.get(i);
			}
		}
		
		String output = "(succ: " + input + ")";
		System.out.println(output);
	}
}
//An instruction, along with its metadata.
class Instruction
{
	public Instruction(String name) 
	{
		this.name = name;
	}
	
	private int target;
	private int blockNum;
	private int opcode;
	
	private boolean isStart;//Start of a block?
	private boolean isEnd;//End of a block?

	private String name;
	
	public int getBlockNum() 
	{
		return blockNum;
	}

	public void setBlockNum(int blockNum) 
	{
		this.blockNum = blockNum;
	}
	
	private boolean isNewBlock;
	public boolean isNewBlock() 
	{
		return isNewBlock;
	}

	public void setNewBlock(boolean isNewBlock) 
	{
		this.isNewBlock = isNewBlock;
	}

	public int getTarget() 
	{
		return target;
	}

	public void setTarget(int target) 
	{
		this.target = target;
	}

	public String getName() 
	{
		return name;
	}

	public void setName(String name) 
	{
		this.name = name;
	}
	
	public int getOpcode() 
	{
		return opcode;
	}

	public void setOpcode(int opcode)
	{
		this.opcode = opcode;
	}

	
	public boolean isStart() 
	{
		return isStart;
	}

	public void setStart(boolean isStart) 
	{
		this.isStart = isStart;
	}

	public boolean isEnd()//End of block? 
	{
		return isEnd;
	}

	public void setEnd(boolean isEnd) 
	{
		this.isEnd = isEnd;
	}
}
/*
 * This class analyzes a classnode for its method instructions and their corresponding control transfer instructions in order to
 * identify Java Basic Blocks. These blocks are differentiated based on their frames. When a basic block is identified, its successors
 * will also be identified (see idSuccessors documentation). Each basic block is indicated by its block number, which is a value that
 * starts at 0 for each method. The basic blocks are given a successor declaration, which explains which basic block(s) follow the current
 * one. JumpInsnNodes are the only nodes that contain a label, thus, they are filtered from the array of classnode.methods instructions.
 * This class makes use of a printwriter to translate a node's name into readable text.  
 */
public class Blocker implements Opcodes
{
	private static Printer printer = new Textifier();
    private static TraceMethodVisitor tmv = new TraceMethodVisitor(printer); 
    private static Instruction[] methodIns;
    private static int methodAmount;
    private static int blockCount = 0;
    private static AbstractInsnNode[] j;//translation array
    private static BlockHeader[] bh;//holds succ blocks for each block
    private static Instruction temp;
    //private static int totalEdges = 0;
    //private static int totalBlocks = 0;
    
    private static ClassReader cr;
    private static ClassNode cn;
    
   public static void main(String[] args) throws Exception
   {
        
        cr = new ClassReader(new FileInputStream(args[0]));//reads in file name and path
        cn = new ClassNode();
        cr.accept(cn,0);
        
        @SuppressWarnings("unchecked")
        List<MethodNode> methods = cn.methods;//list of all methods
        methodAmount = methods.size();
      
        for(int i = 0; i < methodAmount; i++)
        {
        	System.out.println("\nStart of Method: " + methods.get(i).name);
        	analyzeMethod(methods.get(i));
        	System.out.println("End of Method: " + methods.get(i).name);
        	//System.out.println("Total Blocks in " + methods.get(i).name + ": " +  totalBlocks + " \nTotal Edges in " + methods.get(i).name + ": "
        			//+  totalEdges);
        	//System.out.println("\nCyclomatic Complexity: ");
        } 
   }
    /*
     * Takes in a method and stores its instruction information into a translation array, methodIns. An Instruction class is used
     * to hold more information. 
     */
    private static void analyzeMethod(MethodNode m)
    {
    	blockCount = 1;
    	j = m.instructions.toArray();//holds array of ins, its a translation array.
    	methodIns = new Instruction[m.instructions.size()];//array full of ins
    	/* Iterate through and see if the instruction is a goto. if it is, then get its label and record it. if not, set 
    	 * target to -1. The methodIns array will hold the ins number, the string of the opcode, and the target (if a jump).
    	 */
    	for(int i = 0; i < j.length; i++)
    	{
    		temp = new Instruction(extractInsfromNode(j[i]));
    		
    		//If this is a frame (new block). Frames always indicate a new basic block
    		if((j[i].getType() == AbstractInsnNode.FRAME))
    		{
    			blockCount++;
    			//totalBlocks++;
    			temp.setStart(true);//Indicate start of basic block
    		}
    		
    		if(j[i].getOpcode() == GOTO||(isConditional(j[i].getOpcode())))
    		{
    			LabelNode label = ((JumpInsnNode)j[i]).label;
    			label.resetLabel();
    			temp.setTarget(m.instructions.indexOf(label) + 2);//offset of 2 needed. Goto contains 2 lineNumberNodes afterwards.
    			//System.out.println(m.instructions.indexOf(j[i]) + " " + extractInsfromNode(j[i]) + " Jumps to " + (m.instructions.indexOf(label) + 2));	
    		}
    		else
    		{
    			//System.out.println(m.instructions.indexOf(j[i]) + " " + extractInsfromNode(j[i]));
    			temp.setTarget(-1);
    		}
    	
    		//Fill up the temp
    		temp.setOpcode(j[i].getOpcode());
    		temp.setName(extractInsfromNode(j[i]));
    		temp.setBlockNum(blockCount);
    		/*
    		 * If this ins is a conditional, then the new block starts after it. Therefore, blockCount should be updated AFTER
    		 * the conditional ins is added to the array.
    		 */
    		if(isConditional(j[i].getOpcode()))
			{
				temp.setEnd(true);
				blockCount++;
				//totalBlocks++;
			}
    		methodIns[i] = temp;	
    	}
    	
    	//formatBlocks();//make the blocks nice and pretty
    	idSuccessors();//id the blocks reachable by goto ins
    	printNicely();
    }
    /*
     * Prints out the instructions....nicely.
     */
    private static void printNicely()
    {
    	for(int i = 0; i < methodIns.length; i++)
    	{
    		Instruction in = methodIns[i];
    		if(in.isStart())//indicates this ins starts a new block
			{
    				bh[in.getBlockNum()-1].print();
			}	
    		if(in.getOpcode() > 0 )//not a lineNumberNode
    		{
	    			System.out.print("   " + in.getBlockNum() + ":" + in.getName());
    		}
    		if(in.isEnd())//indicates this ins ends a block, but is still inside it.
    		{
    			bh[in.getBlockNum()].print();
    		}	
    	}
    }
    /*
     * Goes through each instruction, and if that instruction has a label (ie: Goto or conditional), then the 
     * label's target instruction index is recorded and saved. Then, the index is correlated to the target's
     * basic block number, which allows for identifying succession. BlockHeader[] stores an array, one index
     * for each basic block, and adds to its linked list each time a link between jump instruction and target
     * is found. If a basic block is found to have no successors, then the next numerical block is assumed to be 
     * its successor.
     */
    private static void idSuccessors()
    {
    	//find the goto target's block
    	//go through each blockheader and assign successors that point to it
    	bh = new BlockHeader[blockCount];
    	
    	initializeArray();
    	Instruction in;
    	
    		//go through each jump ins, and see if it targets the block
    		for(int i = 0; i < methodIns.length; i++)
    		{
    			in = methodIns[i];
    			if(in.getTarget() > 0)//excludes lineNumberNodes
    			{
    				/*
    				 * Conditionals are special. When seen, the label of the conditional only points to one instruction. So,
    				 * it is assumed that the instruction following the conditional is the other path.
    				 */
    				if(isConditional(in.getOpcode()))
    				{
    					bh[in.getBlockNum()].addSucc(in.getBlockNum()+1);
    				}
    				
    				/*
    				 * bh[whatever block this ins belongs to].addSucc(add target blockNum, which is taken from methodIns[])
    				 */
    				bh[in.getBlockNum()].addSucc(methodIns[in.getTarget()].getBlockNum());
    			}
    			//System.out.println(temp.getName() + " goes to index " + temp.getTarget() + " which should be " + extractInsfromNode(j[temp.getTarget()]));
    		}
    		/*
    		 * Go through the known blocks, and if one doesnt have a succ, assume it flows into the next block
    		 */
    		for(int ii = 0; ii < bh.length; ii++)
    		{
    			if(bh[ii].isEmpty())
    			{
    				if(ii < blockCount-1)//bh[] starts from index 0 - this offsets it.
    				{
    					bh[ii].addSucc(bh[ii+1].getBlockNum());
    				}
    			}
    			//bh[ii].printContents();
    		}
    }
    
    //Ensures no null pointer exceptions
    private static void initializeArray()
    {
    	for(int i = 0; i < bh.length; i++)
    	{
    		bh[i] = new BlockHeader(i);
    	}
    }

    //checks if the opcode is a conditional
    private static boolean isConditional(int opcode)
    {	
    	switch(opcode)
    	{
    		case 165: return true; 
    		case 166: return true;
    		case 159: return true;
    		case 162: return true;
    		case 163: return true;
    		case 164: return true;
    		case 161: return true;
    		case 160: return true;
    		case 153: return true;
    		case 156: return true;
    		case 157: return true;
    		case 158: return true;
    		case 155: return true;
    		case 154: return true;
    		case 199: return true;
    		case 198: return true;
    	}
    	return false;
    }
    
    //Takes in the instruction and prints its actual bytecode representation in String format
    public static String extractInsfromNode(AbstractInsnNode insn)
    {
        insn.accept(tmv);
        StringWriter sw = new StringWriter();
        //If opcode is not there, then it will not print. This will only print instructions and not lineNumberNodes
        if(insn.getOpcode() > 0)
        {
        	printer.print(new PrintWriter(sw));
        }
        //printer.print(new PrintWriter(sw));
        printer.getText().clear();//cleans up
        
        return sw.toString();
    }
}
