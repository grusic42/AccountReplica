/*
 * The Spread Toolkit.
 *     
 * The contents of this file are subject to the Spread Open-Source
 * License, Version 1.0 (the ``License''); you may not use
 * this file except in compliance with the License.  You may obtain a
 * copy of the License at:
 *
 * http://www.spread.org/license/
 *
 * or in the file ``license.txt'' found in this distribution.
 *
 * Software distributed under the License is distributed on an AS IS basis, 
 * WITHOUT WARRANTY OF ANY KIND, either express or implied. See the License 
 * for the specific language governing rights and limitations under the 
 * License.
 *
 * The Creators of Spread are:
 *  Yair Amir, Michal Miskin-Amir, Jonathan Stanton, John Schultz.
 *
 *  Copyright (C) 1993-2016 Spread Concepts LLC <info@spreadconcepts.com>
 *
 *  All Rights Reserved.
 *
 * Major Contributor(s):
 * ---------------
 *    Amy Babay            babay@cs.jhu.edu - accelerated ring protocol.
 *    Ryan Caudy           rcaudy@gmail.com - contributions to process groups.
 *    Claudiu Danilov      claudiu@acm.org - scalable wide area support.
 *    Cristina Nita-Rotaru crisn@cs.purdue.edu - group communication security.
 *    Theo Schlossnagle    jesus@omniti.com - Perl, autoconf, old skiplist.
 *    Dan Schoenblum       dansch@cnds.jhu.edu - Java interface.
 *
 */


import spread.*;
import java.net.*;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;
import java.util.Scanner;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;
import java.io.*;
import java.math.RoundingMode;


public class AccountReplica
{
	
	// The Spread Connection.
	/////////////////////////
	private SpreadConnection connection;
	
	// The keyboard input.
	//////////////////////
	private InputStreamReader keyboard;
	Scanner scan;
	
	// A unique client name.
	///////////
	private String user;
	
	// A group.
	///////////
	private SpreadGroup group;
	
	// Number of clients
	private static int clients;
	// Minimum number of clients/replicas
	private static int minimumReplicas;
	// Used so that no messages are sent before minimum required users are connected
	private static boolean minimumReached = false;
	
	// balance on the account. can also be negative
	public double balance;
	// counts number of orders since startup 
	public int orderCounter;
	// counts number of outstanding transactions, meaning orders that have finish to achieve consistency between replicas.
	public int outstandingCounter;
	// a list of outstanding transactions.
	public Collection<Transaction> outstandingCollection;
	// a list of executed transactions.
	public List<Transaction> executedList;
	// Executor that sends outstanding orders every 10 seconds.
	public ScheduledExecutorService executor;
	
	public static String inputfile;
	public BufferedReader br;

	private void PrintMenu()
	{
		// Print the menu.
		//////////////////
		System.out.print("\n" +
						 "==========\n" +
						 "Account Replica ["+ group.toString() + "] Menu:\n" +
						 "==========\n" +
						 "\n" +
						 "\tbalance -- print account balance\n" + 
						 "\tdeposit <amount> -- deposit to account\n" +
						 "\taddInterest <percent> -- adds interest to balance\n" +
						 "\n" +
						 "\tgetHistory -- print recent transactions\n" + 
						 "\tcleanHistory -- empty history list\n" +
						 "\tmemberinfo -- print current participating replicas\n" +
						 "\n");
	
		
		System.out.print("\texit -- quit\n");
	}

	// Print this membership data.  Does so in a generic way so identical
	// function is used in recThread and User. 
	private void printMembershipInfo(MembershipInfo info) 
	{
	        SpreadGroup group = info.getGroup();
		if(info.isRegularMembership()) {
			SpreadGroup members[] = info.getMembers();
			MembershipInfo.VirtualSynchronySet virtual_synchrony_sets[] = info.getVirtualSynchronySets();
			MembershipInfo.VirtualSynchronySet my_virtual_synchrony_set = info.getMyVirtualSynchronySet();

			System.out.println("REGULAR membership for group " + group +
					   " with " + members.length + " members:");
			for( int i = 0; i < members.length; ++i ) {
				System.out.println("\t\t" + members[i]);
			}
			System.out.println("Group ID is " + info.getGroupID());

			System.out.print("\tDue to ");
			if(info.isCausedByJoin()) {
				clients = info.getMembers().length;
				if (minimumReached) {
					// If new member, make sure they have same balance as rest of the group
					SpreadMessage msg = new SpreadMessage();
					byte mess[] = new String("balance " + Double.toString(balance)).getBytes();

					msg.setData(mess);
					msg.setReliable();
					msg.addGroup(group);
					try {
						connection.multicast(msg);
					} catch (SpreadException e) {
						e.printStackTrace();
					}
				}
				System.out.println("the JOIN of " + info.getJoined());
			}	else if(info.isCausedByLeave()) {
				clients = info.getMembers().length;
				System.out.println("the LEAVE of " + info.getLeft());
			}	else if(info.isCausedByDisconnect()) {
				clients = info.getMembers().length;
				System.out.println("the DISCONNECT of " + info.getDisconnected());
			} else if(info.isCausedByNetwork()) {
				System.out.println("NETWORK change");
				for( int i = 0 ; i < virtual_synchrony_sets.length ; ++i ) {
					MembershipInfo.VirtualSynchronySet set = virtual_synchrony_sets[i];
					SpreadGroup         setMembers[] = set.getMembers();
					System.out.print("\t\t");
					if( set == my_virtual_synchrony_set ) {
						System.out.print( "(LOCAL) " );
					} else {
						System.out.print( "(OTHER) " );
					}
					System.out.println( "Virtual Synchrony Set " + i + " has " +
							    set.getSize() + " members:");
					for( int j = 0; j < set.getSize(); ++j ) {
						System.out.println("\t\t\t" + setMembers[j]);
					}
				}
			}
		} else if(info.isTransition()) {
			System.out.println("TRANSITIONAL membership for group " + group);
		} else if(info.isSelfLeave()) {
			System.out.println("SELF-LEAVE message for group " + group);
		}
	}
	
	private void UserCommand()
	{
		String[] command = null;
		
		try {
			if (inputfile!= null && br.ready() ) {
				String line=null;
				try {
					line = br.readLine();
				} catch (IOException e) {
					e.printStackTrace();
				}
				command = line.split(" ");
			}
			else if (inputfile!= null && !br.ready()) {
				System.exit(0);
			}
			
			else {
				// Show the prompt.
				///////////////////
				System.out.print("\n" + 
								 "User> ");
			
				// Get the input.
				/////////////////
				String input = scan.nextLine();
				command = input.split(" ");
			}
		} catch (IOException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		
		Transaction transaction;

		// Check what it is.
		////////////////////
		//SpreadMessage msg;
		try
		{
			switch(command[0])
			{
			//BALANCE
			case "balance":
				// Checks the account balance
				//////////////////
				System.out.println(getBalance());
				
				break;
				
			//DEPOSIT
			case "deposit":
				// Deposit into account.
				///////////////////
				try {
					double amount = Double.parseDouble(command[1]); 
					
					transaction = new Transaction();
					transaction.command = (command[0] + " " + amount);
					outstandingCounter++;
					transaction.uniqueID = (user + "#" + outstandingCounter);
					outstandingCollection.add(transaction);
					
				}
				catch (NumberFormatException e)
				{
					System.err.println("2nd argument: amount to deposit needs to be a number.");
					e.printStackTrace();
				}
				
				break;
				
			//ADD INTEREST
			case "addInterest":
				// Adds a percentage-wise interest to the balance.
				//////////////////////////////
				
				try {
					//send message, the rest here is done in recThread?
					double rate = Double.parseDouble(command[1]);
					
					transaction = new Transaction();
					transaction.command = (command[0] + " " + rate);
					outstandingCounter++;
					transaction.uniqueID = (user + " " + outstandingCounter);
					outstandingCollection.add(transaction);
					
				}
				catch (NumberFormatException e)
				{
					System.err.println("2nd argument: interest rate needs to be a number.");
					e.printStackTrace();
				}
				
				break;
			
			
			//GET HITORY
			case "getHistory":				
				// Prints out recent transactions
				//////////////////////////////
				printHistory();
				
				break;
			
				
			//CLEAR HISTORY
			case "cleanHistory":
				// Clears executedList, not outstandingCollection and counters.
				executedList.clear();
				
				break;
				
			
			//MEMBERINFO
			case "memberInfo":
				
				
				break;
			
			//QUIT
			case "exit":
				// Leave group
				//////////////
				group.leave();
				
				// Disconnect.
				//////////////
				connection.disconnect();
				
				// Quit.
				////////
				System.exit(0);
				
				break;
				
			default:
				// Unknown command.
				///////////////////
				System.out.println("Unknown command");
				
				// Show the menu again.
				///////////////////////
				PrintMenu();
			}
		}
		catch(Exception e)
		{
			e.printStackTrace();
			System.exit(1);
		}
	}
	
	public AccountReplica(String user, String address, int port, String groupName)
	{
		// Setup the keyboard input.
		////////////////////////////
		keyboard = new InputStreamReader(System.in);
		scan = new Scanner(System.in);
		
		// Establish the spread connection & initialize values
		///////////////////////////////////
		try
		{
			connection = new SpreadConnection();
			connection.connect(InetAddress.getByName(address), port, user, false, true);
			
			group = new SpreadGroup();
			group.join(connection, groupName);
			System.out.println("Joined " + group + ".");
			
			this.user = user;
			
			balance = 0.0;
			orderCounter = 0;
			outstandingCounter = 0;
			
			outstandingCollection = new LinkedList<Transaction>();
			executedList = new ArrayList<Transaction>();
			
			executor = Executors.newScheduledThreadPool(1);
			executor.scheduleAtFixedRate(outstandingRunnable, 0, 10, TimeUnit.SECONDS);
			
			if (inputfile != null) {
				br = new BufferedReader(new FileReader(inputfile));
				System.out.println(inputfile);
			}
			minimumReached = false;
		}
		catch(SpreadException e)
		{
			System.err.println("There was an error connecting to the daemon.");
			e.printStackTrace();
			System.exit(1);
		}
		catch(UnknownHostException e)
		{
			System.err.println("Can't find the daemon " + address);
			System.exit(1);
		} catch (FileNotFoundException e) {
			System.err.println("Input file not found");
			e.printStackTrace();
		}
		
		connection.add(new BasicMessageListener() {
			public void messageReceived(SpreadMessage msg)
			{
				try
				{
		   		        //System.out.println("***************** Received Message************");
					if(msg.isRegular())
					{/*
						System.out.print("Received a ");
						if(msg.isUnreliable())
							System.out.print("UNRELIABLE");
						else if(msg.isReliable())
							System.out.print("RELIABLE");
						else if(msg.isFifo())
							System.out.print("FIFO");
						else if(msg.isCausal())
							System.out.print("CAUSAL");
						else if(msg.isAgreed())
							System.out.print("AGREED");
						else if(msg.isSafe())
							System.out.print("SAFE");
						System.out.println(" message.\n");
						*/
						//System.out.println("Sent by  " + msg.getSender() + ".");
						
						//System.out.println("Type is " + msg.getType() + ".");
						/*
						if(msg.getEndianMismatch() == true)
							System.out.println("There is an endian mismatch.");
						else
							System.out.println("There is no endian mismatch.");
						*/
						SpreadGroup groups[] = msg.getGroups();
						//System.out.println("To " + groups.length + " groups.");
						
						byte data[] = msg.getData();
						//System.out.println("The data is " + data.length + " bytes.");
						
						//System.out.println("The message is: " + new String(data));
						Transaction t;
						String str [] = new String(data).split(" ");
						switch(str[0])
						{
							//BALANCE - will overwrite balance when a new user arrives. 
							case "balance":
								balance = (Double.parseDouble(str[1]));
								
								break;
							
							//DEPOSIT
							case "deposit":
								
								t = new Transaction();
								t.command = str[0] + " " + str[1];
								t.uniqueID = str[2];
								
								executedList.add(t);
								orderCounter += 1;
								deposit(Double.parseDouble(str[1]));

								break;
							
							
							//ADD INTEREST
							case "addInterest":
								
								t = new Transaction();
								t.command = str[0] + " " + str[1];
								t.uniqueID = str[2];
								
								executedList.add(t);
								orderCounter += 1;
								addInterest(Double.parseDouble(str[1]));
								
							break;
						}
					}
					else if ( msg.isMembership() )
					{
						MembershipInfo info = msg.getMembershipInfo();
						printMembershipInfo(info);
					} else if ( msg.isReject() )
					{
					     /*    //Received a Reject message 
						System.out.print("Received a ");
						if(msg.isUnreliable())
							System.out.print("UNRELIABLE");
						else if(msg.isReliable())
							System.out.print("RELIABLE");
						else if(msg.isFifo())
							System.out.print("FIFO");
						else if(msg.isCausal())
							System.out.print("CAUSAL");
						else if(msg.isAgreed())
							System.out.print("AGREED");
						else if(msg.isSafe())
							System.out.print("SAFE");
						System.out.println(" REJECTED message.\n");
						*/
						//System.out.println("Sent by  " + msg.getSender() + ".");
						
						//System.out.println("Type is " + msg.getType() + ".");
						/*
						if(msg.getEndianMismatch() == true)
							System.out.println("There is an endian mismatch.");
						else
							System.out.println("There is no endian mismatch.");
						*/
						SpreadGroup groups[] = msg.getGroups();
						//System.out.println("To " + groups.length + " groups.");
						
						byte data[] = msg.getData();
						//System.out.println("The data is " + data.length + " bytes.");
						
						//System.out.println("The message is: " + new String(data));
					} else {
					    System.out.println("Message is of unknown type: " + msg.getServiceType() );
					}
				}
				catch(Exception e)
				{
					e.printStackTrace();
					System.exit(1);
				}
			}
		});

		while (minimumReached == false ) { //|| clients < minimumReplicas ) {
			try {
				if (clients >= minimumReplicas) {
					minimumReached = true;
					
				}
				System.out.println("\nNot enough clients to run. Need " + (minimumReplicas - clients) + " more. \n"
							+ "Will try again in 6 seconds.\n");
				Thread.sleep(6000);
							
			} catch (InterruptedException e) {
				e.printStackTrace();
			}
		}
		//minimumReached = true;
		
		// Show the menu.
		/////////////////
		PrintMenu();
		
		
		// if inputfile given, read line by line..
		//if file //while
		
		// Get a user command.
		//////////////////////
		//else 
		
		while(true)
		{
			UserCommand();

		}
		
	}
	
	Runnable outstandingRunnable = new Runnable() {
	    public void run() {
	        for(Transaction t : outstandingCollection) {
	        	String str = t.command + " " + t.uniqueID;
	        	//send message
	    		SpreadMessage msg = new SpreadMessage();
				msg.setSafe();
				msg.addGroup(group);
				msg.setData(new String(str).getBytes());
				
				try {
					connection.multicast(msg);
				} catch (SpreadException e) {
					System.out.println("Unable to connect with Spread daemon");
					e.printStackTrace();
				}
	        	
	        }
	        outstandingCollection.clear();
	        outstandingCounter = 0;
	    }
	};
	
	public String getBalance() {
		DecimalFormat df = new DecimalFormat("#.##");
		df.setRoundingMode(RoundingMode.CEILING);
		return df.format(balance);
	}
	
	public void deposit(double amount) {
		balance += amount;
	}
	
	public void addInterest (double percent) {
		balance = balance * (1 + (percent/100));
	}
	
	public void printHistory () {
		int index = 1;
		for(Transaction t : executedList) {
			System.out.println(index + ". " + t.toString());
			index++;
		}
		System.out.print("\n");
		for(Transaction t : outstandingCollection) {
			System.out.println(t.toString());
		}
		
	}	
	
	// memberinfo ()
	// sleep <duration> ()
	
	
	public final static void main(String[] args)
	{			
		// finds a unique name/id for user
		Random rand = new Random();
		String user = "User" + String.valueOf(rand.nextInt(100));
		
		String[] tokens = args[0].split(":");
		String address = tokens[0];
		int port = Integer.parseInt(tokens[1]);
		
		String accountName = args[1]; // In Spread -> same as group name
		minimumReplicas = Integer.parseInt(args[2]);
		
		System.out.println(user + " " + address + " " + port + " " + accountName + " " + minimumReplicas);
		
		if (minimumReplicas < 1) {
			System.out.print("Usage: \n" + 
							 "\t[<address>:<port>]     : the name or IP + port for the daemon\n" + 
							 "\t[<accountName>]        : the accountName for the group\n" +
							 "\t[<numberReplicas>]     : the no. of account replicas before starting. Minimum 3.\n" +
							 "\t[<filepath>](optional) : filepath for batch input\n");
			System.exit(0);
		}
		if (args.length == 4) {
			AccountReplica.inputfile = args[3];
		}
		else AccountReplica.inputfile = null;

		AccountReplica ar = new AccountReplica(user, address, port, accountName);		
	}
}
