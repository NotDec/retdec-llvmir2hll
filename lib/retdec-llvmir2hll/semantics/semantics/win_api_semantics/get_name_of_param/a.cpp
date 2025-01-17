/**
* @file src/llvmir2hll/semantics/semantics/win_api_semantics/get_name_of_param/a.cpp
* @brief Implementation of the initialization of WinAPI functions.
* @copyright (c) 2017 Avast Software, licensed under the MIT license
*/

#include "retdec-llvmir2hll/semantics/semantics/win_api_semantics/get_name_of_param/a.h"

namespace retdec {
namespace llvmir2hll {
namespace semantics {
namespace win_api {

/**
* @brief Initializes the given map with info about functions starting with A or
*        underscore.
*/
void initFuncParamNamesMap_A(FuncParamNamesMap &funcParamNamesMap) {
	//
	// windows.h
	//
	ADD_PARAM_NAME("_hread", 1, "hFile"); // HFILE
	ADD_PARAM_NAME("_hread", 2, "lpBuffer"); // LPVOID
	ADD_PARAM_NAME("_hread", 3, "lBytes"); // __LONG32
	ADD_PARAM_NAME("_hwrite", 1, "hFile"); // HFILE
	ADD_PARAM_NAME("_hwrite", 2, "lpBuffer"); // LPCCH
	ADD_PARAM_NAME("_hwrite", 3, "lBytes"); // __LONG32
	ADD_PARAM_NAME("_lclose", 1, "hFile"); // HFILE
	ADD_PARAM_NAME("_lcreat", 1, "lpPathName"); // LPCSTR
	ADD_PARAM_NAME("_lcreat", 2, "iAttribute"); // int
	ADD_PARAM_NAME("_llseek", 1, "hFile"); // HFILE
	ADD_PARAM_NAME("_llseek", 2, "lOffset"); // LONG
	ADD_PARAM_NAME("_llseek", 3, "iOrigin"); // int
	ADD_PARAM_NAME("_lopen", 1, "lpPathName"); // LPCSTR
	ADD_PARAM_NAME("_lopen", 2, "iReadWrite"); // int
	ADD_PARAM_NAME("_lread", 1, "hFile"); // HFILE
	ADD_PARAM_NAME("_lread", 2, "lpBuffer"); // LPVOID
	ADD_PARAM_NAME("_lread", 3, "uBytes"); // UINT
	ADD_PARAM_NAME("_lwrite", 1, "hFile"); // HFILE
	ADD_PARAM_NAME("_lwrite", 2, "lpBuffer"); // LPCCH
	ADD_PARAM_NAME("_lwrite", 3, "uBytes"); // UINT

	ADD_PARAM_NAME("AbortDoc", 1, "hdc"); // HDC
	ADD_PARAM_NAME("AbortPath", 1, "hdc"); // HDC
	ADD_PARAM_NAME("AbortPrinter", 1, "hPrinter"); // HANDLE
	ADD_PARAM_NAME("AbortSystemShutdownA", 1, "lpMachineName"); // LPSTR
	ADD_PARAM_NAME("AbortSystemShutdownW", 1, "lpMachineName"); // LPWSTR
	ADD_PARAM_NAME("AcceptEx", 1, "sListenSocket"); // SOCKET
	ADD_PARAM_NAME("AcceptEx", 2, "sAcceptSocket"); // SOCKET
	ADD_PARAM_NAME("AcceptEx", 3, "lpOutputBuffer"); // PVOID
	ADD_PARAM_NAME("AcceptEx", 4, "dwReceiveDataLength"); // DWORD
	ADD_PARAM_NAME("AcceptEx", 5, "dwLocalAddressLength"); // DWORD
	ADD_PARAM_NAME("AcceptEx", 6, "dwRemoteAddressLength"); // DWORD
	ADD_PARAM_NAME("AcceptEx", 7, "lpdwBytesReceived"); // LPDWORD
	ADD_PARAM_NAME("AcceptEx", 8, "lpOverlapped"); // LPOVERLAPPED
	ADD_PARAM_NAME("AccessCheck", 1, "pSecurityDescriptor"); // PSECURITY_DESCRIPTOR
	ADD_PARAM_NAME("AccessCheck", 2, "ClientToken"); // HANDLE
	ADD_PARAM_NAME("AccessCheck", 3, "DesiredAccess"); // DWORD
	ADD_PARAM_NAME("AccessCheck", 4, "GenericMapping"); // PGENERIC_MAPPING
	ADD_PARAM_NAME("AccessCheck", 5, "PrivilegeSet"); // PPRIVILEGE_SET
	ADD_PARAM_NAME("AccessCheck", 6, "PrivilegeSetLength"); // LPDWORD
	ADD_PARAM_NAME("AccessCheck", 7, "GrantedAccess"); // LPDWORD
	ADD_PARAM_NAME("AccessCheck", 8, "AccessStatus"); // LPBOOL
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmA", 1, "SubsystemName"); // LPCSTR
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmA", 2, "HandleId"); // LPVOID
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmA", 3, "ObjectTypeName"); // LPSTR
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmA", 4, "ObjectName"); // LPSTR
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmA", 5, "SecurityDescriptor"); // PSECURITY_DESCRIPTOR
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmA", 6, "DesiredAccess"); // DWORD
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmA", 7, "GenericMapping"); // PGENERIC_MAPPING
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmA", 8, "ObjectCreation"); // WINBOOL
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmA", 9, "GrantedAccess"); // LPDWORD
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmA", 10, "AccessStatus"); // LPBOOL
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmA", 11, "pfGenerateOnClose"); // LPBOOL
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmW", 1, "SubsystemName"); // LPCWSTR
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmW", 2, "HandleId"); // LPVOID
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmW", 3, "ObjectTypeName"); // LPWSTR
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmW", 4, "ObjectName"); // LPWSTR
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmW", 5, "SecurityDescriptor"); // PSECURITY_DESCRIPTOR
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmW", 6, "DesiredAccess"); // DWORD
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmW", 7, "GenericMapping"); // PGENERIC_MAPPING
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmW", 8, "ObjectCreation"); // WINBOOL
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmW", 9, "GrantedAccess"); // LPDWORD
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmW", 10, "AccessStatus"); // LPBOOL
	ADD_PARAM_NAME("AccessCheckAndAuditAlarmW", 11, "pfGenerateOnClose"); // LPBOOL
	ADD_PARAM_NAME("AccessCheckByType", 1, "pSecurityDescriptor"); // PSECURITY_DESCRIPTOR
	ADD_PARAM_NAME("AccessCheckByType", 2, "PrincipalSelfSid"); // PSID
	ADD_PARAM_NAME("AccessCheckByType", 3, "ClientToken"); // HANDLE
	ADD_PARAM_NAME("AccessCheckByType", 4, "DesiredAccess"); // DWORD
	ADD_PARAM_NAME("AccessCheckByType", 5, "ObjectTypeList"); // POBJECT_TYPE_LIST
	ADD_PARAM_NAME("AccessCheckByType", 6, "ObjectTypeListLength"); // DWORD
	ADD_PARAM_NAME("AccessCheckByType", 7, "GenericMapping"); // PGENERIC_MAPPING
	ADD_PARAM_NAME("AccessCheckByType", 8, "PrivilegeSet"); // PPRIVILEGE_SET
	ADD_PARAM_NAME("AccessCheckByType", 9, "PrivilegeSetLength"); // LPDWORD
	ADD_PARAM_NAME("AccessCheckByType", 10, "GrantedAccess"); // LPDWORD
	ADD_PARAM_NAME("AccessCheckByType", 11, "AccessStatus"); // LPBOOL
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmA", 1, "SubsystemName"); // LPCSTR
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmA", 2, "HandleId"); // LPVOID
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmA", 3, "ObjectTypeName"); // LPCSTR
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmA", 4, "ObjectName"); // LPCSTR
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmA", 5, "SecurityDescriptor"); // PSECURITY_DESCRIPTOR
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmA", 6, "PrincipalSelfSid"); // PSID
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmA", 7, "DesiredAccess"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmA", 8, "AuditType"); // AUDIT_EVENT_TYPE
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmA", 9, "Flags"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmA", 10, "ObjectTypeList"); // POBJECT_TYPE_LIST
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmA", 11, "ObjectTypeListLength"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmA", 12, "GenericMapping"); // PGENERIC_MAPPING
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmA", 13, "ObjectCreation"); // WINBOOL
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmA", 14, "GrantedAccess"); // LPDWORD
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmA", 15, "AccessStatus"); // LPBOOL
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmA", 16, "pfGenerateOnClose"); // LPBOOL
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmW", 1, "SubsystemName"); // LPCWSTR
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmW", 2, "HandleId"); // LPVOID
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmW", 3, "ObjectTypeName"); // LPCWSTR
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmW", 4, "ObjectName"); // LPCWSTR
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmW", 5, "SecurityDescriptor"); // PSECURITY_DESCRIPTOR
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmW", 6, "PrincipalSelfSid"); // PSID
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmW", 7, "DesiredAccess"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmW", 8, "AuditType"); // AUDIT_EVENT_TYPE
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmW", 9, "Flags"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmW", 10, "ObjectTypeList"); // POBJECT_TYPE_LIST
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmW", 11, "ObjectTypeListLength"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmW", 12, "GenericMapping"); // PGENERIC_MAPPING
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmW", 13, "ObjectCreation"); // WINBOOL
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmW", 14, "GrantedAccess"); // LPDWORD
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmW", 15, "AccessStatus"); // LPBOOL
	ADD_PARAM_NAME("AccessCheckByTypeAndAuditAlarmW", 16, "pfGenerateOnClose"); // LPBOOL
	ADD_PARAM_NAME("AccessCheckByTypeResultList", 1, "pSecurityDescriptor"); // PSECURITY_DESCRIPTOR
	ADD_PARAM_NAME("AccessCheckByTypeResultList", 2, "PrincipalSelfSid"); // PSID
	ADD_PARAM_NAME("AccessCheckByTypeResultList", 3, "ClientToken"); // HANDLE
	ADD_PARAM_NAME("AccessCheckByTypeResultList", 4, "DesiredAccess"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultList", 5, "ObjectTypeList"); // POBJECT_TYPE_LIST
	ADD_PARAM_NAME("AccessCheckByTypeResultList", 6, "ObjectTypeListLength"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultList", 7, "GenericMapping"); // PGENERIC_MAPPING
	ADD_PARAM_NAME("AccessCheckByTypeResultList", 8, "PrivilegeSet"); // PPRIVILEGE_SET
	ADD_PARAM_NAME("AccessCheckByTypeResultList", 9, "PrivilegeSetLength"); // LPDWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultList", 10, "GrantedAccessList"); // LPDWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultList", 11, "AccessStatusList"); // LPDWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmA", 1, "SubsystemName"); // LPCSTR
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmA", 2, "HandleId"); // LPVOID
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmA", 3, "ObjectTypeName"); // LPCSTR
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmA", 4, "ObjectName"); // LPCSTR
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmA", 5, "SecurityDescriptor"); // PSECURITY_DESCRIPTOR
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmA", 6, "PrincipalSelfSid"); // PSID
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmA", 7, "DesiredAccess"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmA", 8, "AuditType"); // AUDIT_EVENT_TYPE
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmA", 9, "Flags"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmA", 10, "ObjectTypeList"); // POBJECT_TYPE_LIST
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmA", 11, "ObjectTypeListLength"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmA", 12, "GenericMapping"); // PGENERIC_MAPPING
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmA", 13, "ObjectCreation"); // WINBOOL
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmA", 14, "GrantedAccess"); // LPDWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmA", 15, "AccessStatusList"); // LPDWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmA", 16, "pfGenerateOnClose"); // LPBOOL
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleA", 1, "SubsystemName"); // LPCSTR
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleA", 2, "HandleId"); // LPVOID
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleA", 3, "ClientToken"); // HANDLE
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleA", 4, "ObjectTypeName"); // LPCSTR
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleA", 5, "ObjectName"); // LPCSTR
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleA", 6, "SecurityDescriptor"); // PSECURITY_DESCRIPTOR
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleA", 7, "PrincipalSelfSid"); // PSID
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleA", 8, "DesiredAccess"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleA", 9, "AuditType"); // AUDIT_EVENT_TYPE
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleA", 10, "Flags"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleA", 11, "ObjectTypeList"); // POBJECT_TYPE_LIST
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleA", 12, "ObjectTypeListLength"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleA", 13, "GenericMapping"); // PGENERIC_MAPPING
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleA", 14, "ObjectCreation"); // WINBOOL
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleA", 15, "GrantedAccess"); // LPDWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleA", 16, "AccessStatusList"); // LPDWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleA", 17, "pfGenerateOnClose"); // LPBOOL
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleW", 1, "SubsystemName"); // LPCWSTR
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleW", 2, "HandleId"); // LPVOID
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleW", 3, "ClientToken"); // HANDLE
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleW", 4, "ObjectTypeName"); // LPCWSTR
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleW", 5, "ObjectName"); // LPCWSTR
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleW", 6, "SecurityDescriptor"); // PSECURITY_DESCRIPTOR
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleW", 7, "PrincipalSelfSid"); // PSID
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleW", 8, "DesiredAccess"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleW", 9, "AuditType"); // AUDIT_EVENT_TYPE
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleW", 10, "Flags"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleW", 11, "ObjectTypeList"); // POBJECT_TYPE_LIST
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleW", 12, "ObjectTypeListLength"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleW", 13, "GenericMapping"); // PGENERIC_MAPPING
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleW", 14, "ObjectCreation"); // WINBOOL
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleW", 15, "GrantedAccess"); // LPDWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleW", 16, "AccessStatusList"); // LPDWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmByHandleW", 17, "pfGenerateOnClose"); // LPBOOL
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmW", 1, "SubsystemName"); // LPCWSTR
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmW", 2, "HandleId"); // LPVOID
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmW", 3, "ObjectTypeName"); // LPCWSTR
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmW", 4, "ObjectName"); // LPCWSTR
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmW", 5, "SecurityDescriptor"); // PSECURITY_DESCRIPTOR
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmW", 6, "PrincipalSelfSid"); // PSID
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmW", 7, "DesiredAccess"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmW", 8, "AuditType"); // AUDIT_EVENT_TYPE
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmW", 9, "Flags"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmW", 10, "ObjectTypeList"); // POBJECT_TYPE_LIST
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmW", 11, "ObjectTypeListLength"); // DWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmW", 12, "GenericMapping"); // PGENERIC_MAPPING
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmW", 13, "ObjectCreation"); // WINBOOL
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmW", 14, "GrantedAccess"); // LPDWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmW", 15, "AccessStatusList"); // LPDWORD
	ADD_PARAM_NAME("AccessCheckByTypeResultListAndAuditAlarmW", 16, "pfGenerateOnClose"); // LPBOOL
	ADD_PARAM_NAME("AcquireSRWLockExclusive", 1, "SRWLock"); // PSRWLOCK
	ADD_PARAM_NAME("AcquireSRWLockShared", 1, "SRWLock"); // PSRWLOCK
	ADD_PARAM_NAME("ActivateActCtx", 1, "hActCtx"); // HANDLE
	ADD_PARAM_NAME("ActivateActCtx", 2, "lpCookie"); // ULONG_PTR *
	ADD_PARAM_NAME("ActivateKeyboardLayout", 1, "hkl"); // HKL
	ADD_PARAM_NAME("ActivateKeyboardLayout", 2, "Flags"); // UINT
	ADD_PARAM_NAME("AddAccessAllowedAce", 1, "pAcl"); // PACL
	ADD_PARAM_NAME("AddAccessAllowedAce", 2, "dwAceRevision"); // DWORD
	ADD_PARAM_NAME("AddAccessAllowedAce", 3, "AccessMask"); // DWORD
	ADD_PARAM_NAME("AddAccessAllowedAce", 4, "pSid"); // PSID
	ADD_PARAM_NAME("AddAccessAllowedAceEx", 1, "pAcl"); // PACL
	ADD_PARAM_NAME("AddAccessAllowedAceEx", 2, "dwAceRevision"); // DWORD
	ADD_PARAM_NAME("AddAccessAllowedAceEx", 3, "AceFlags"); // DWORD
	ADD_PARAM_NAME("AddAccessAllowedAceEx", 4, "AccessMask"); // DWORD
	ADD_PARAM_NAME("AddAccessAllowedAceEx", 5, "pSid"); // PSID
	ADD_PARAM_NAME("AddAccessAllowedObjectAce", 1, "pAcl"); // PACL
	ADD_PARAM_NAME("AddAccessAllowedObjectAce", 2, "dwAceRevision"); // DWORD
	ADD_PARAM_NAME("AddAccessAllowedObjectAce", 3, "AceFlags"); // DWORD
	ADD_PARAM_NAME("AddAccessAllowedObjectAce", 4, "AccessMask"); // DWORD
	ADD_PARAM_NAME("AddAccessAllowedObjectAce", 5, "ObjectTypeGuid"); // GUID *
	ADD_PARAM_NAME("AddAccessAllowedObjectAce", 6, "InheritedObjectTypeGuid"); // GUID *
	ADD_PARAM_NAME("AddAccessAllowedObjectAce", 7, "pSid"); // PSID
	ADD_PARAM_NAME("AddAccessDeniedAce", 1, "pAcl"); // PACL
	ADD_PARAM_NAME("AddAccessDeniedAce", 2, "dwAceRevision"); // DWORD
	ADD_PARAM_NAME("AddAccessDeniedAce", 3, "AccessMask"); // DWORD
	ADD_PARAM_NAME("AddAccessDeniedAce", 4, "pSid"); // PSID
	ADD_PARAM_NAME("AddAccessDeniedAceEx", 1, "pAcl"); // PACL
	ADD_PARAM_NAME("AddAccessDeniedAceEx", 2, "dwAceRevision"); // DWORD
	ADD_PARAM_NAME("AddAccessDeniedAceEx", 3, "AceFlags"); // DWORD
	ADD_PARAM_NAME("AddAccessDeniedAceEx", 4, "AccessMask"); // DWORD
	ADD_PARAM_NAME("AddAccessDeniedAceEx", 5, "pSid"); // PSID
	ADD_PARAM_NAME("AddAccessDeniedObjectAce", 1, "pAcl"); // PACL
	ADD_PARAM_NAME("AddAccessDeniedObjectAce", 2, "dwAceRevision"); // DWORD
	ADD_PARAM_NAME("AddAccessDeniedObjectAce", 3, "AceFlags"); // DWORD
	ADD_PARAM_NAME("AddAccessDeniedObjectAce", 4, "AccessMask"); // DWORD
	ADD_PARAM_NAME("AddAccessDeniedObjectAce", 5, "ObjectTypeGuid"); // GUID *
	ADD_PARAM_NAME("AddAccessDeniedObjectAce", 6, "InheritedObjectTypeGuid"); // GUID *
	ADD_PARAM_NAME("AddAccessDeniedObjectAce", 7, "pSid"); // PSID
	ADD_PARAM_NAME("AddAce", 1, "pAcl"); // PACL
	ADD_PARAM_NAME("AddAce", 2, "dwAceRevision"); // DWORD
	ADD_PARAM_NAME("AddAce", 3, "dwStartingAceIndex"); // DWORD
	ADD_PARAM_NAME("AddAce", 4, "pAceList"); // LPVOID
	ADD_PARAM_NAME("AddAce", 5, "nAceListLength"); // DWORD
	ADD_PARAM_NAME("AddAtomA", 1, "lpString"); // LPCSTR
	ADD_PARAM_NAME("AddAtomW", 1, "lpString"); // LPCWSTR
	ADD_PARAM_NAME("AddAuditAccessAce", 1, "pAcl"); // PACL
	ADD_PARAM_NAME("AddAuditAccessAce", 2, "dwAceRevision"); // DWORD
	ADD_PARAM_NAME("AddAuditAccessAce", 3, "dwAccessMask"); // DWORD
	ADD_PARAM_NAME("AddAuditAccessAce", 4, "pSid"); // PSID
	ADD_PARAM_NAME("AddAuditAccessAce", 5, "bAuditSuccess"); // WINBOOL
	ADD_PARAM_NAME("AddAuditAccessAce", 6, "bAuditFailure"); // WINBOOL
	ADD_PARAM_NAME("AddAuditAccessAceEx", 1, "pAcl"); // PACL
	ADD_PARAM_NAME("AddAuditAccessAceEx", 2, "dwAceRevision"); // DWORD
	ADD_PARAM_NAME("AddAuditAccessAceEx", 3, "AceFlags"); // DWORD
	ADD_PARAM_NAME("AddAuditAccessAceEx", 4, "dwAccessMask"); // DWORD
	ADD_PARAM_NAME("AddAuditAccessAceEx", 5, "pSid"); // PSID
	ADD_PARAM_NAME("AddAuditAccessAceEx", 6, "bAuditSuccess"); // WINBOOL
	ADD_PARAM_NAME("AddAuditAccessAceEx", 7, "bAuditFailure"); // WINBOOL
	ADD_PARAM_NAME("AddAuditAccessObjectAce", 1, "pAcl"); // PACL
	ADD_PARAM_NAME("AddAuditAccessObjectAce", 2, "dwAceRevision"); // DWORD
	ADD_PARAM_NAME("AddAuditAccessObjectAce", 3, "AceFlags"); // DWORD
	ADD_PARAM_NAME("AddAuditAccessObjectAce", 4, "AccessMask"); // DWORD
	ADD_PARAM_NAME("AddAuditAccessObjectAce", 5, "ObjectTypeGuid"); // GUID *
	ADD_PARAM_NAME("AddAuditAccessObjectAce", 6, "InheritedObjectTypeGuid"); // GUID *
	ADD_PARAM_NAME("AddAuditAccessObjectAce", 7, "pSid"); // PSID
	ADD_PARAM_NAME("AddAuditAccessObjectAce", 8, "bAuditSuccess"); // WINBOOL
	ADD_PARAM_NAME("AddAuditAccessObjectAce", 9, "bAuditFailure"); // WINBOOL
	ADD_PARAM_NAME("AddConditionalAce", 1, "pAcl"); // PACL
	ADD_PARAM_NAME("AddConditionalAce", 2, "dwAceRevision"); // DWORD
	ADD_PARAM_NAME("AddConditionalAce", 3, "AceFlags"); // DWORD
	ADD_PARAM_NAME("AddConditionalAce", 4, "AceType"); // UCHAR
	ADD_PARAM_NAME("AddConditionalAce", 5, "AccessMask"); // DWORD
	ADD_PARAM_NAME("AddConditionalAce", 6, "pSid"); // PSID
	ADD_PARAM_NAME("AddConditionalAce", 7, "ConditionStr"); // PWCHAR
	ADD_PARAM_NAME("AddConditionalAce", 8, "ReturnLength"); // DWORD *
	ADD_PARAM_NAME("AddConsoleAliasA", 1, "Source"); // LPSTR
	ADD_PARAM_NAME("AddConsoleAliasA", 2, "Target"); // LPSTR
	ADD_PARAM_NAME("AddConsoleAliasA", 3, "ExeName"); // LPSTR
	ADD_PARAM_NAME("AddConsoleAliasW", 1, "Source"); // LPWSTR
	ADD_PARAM_NAME("AddConsoleAliasW", 2, "Target"); // LPWSTR
	ADD_PARAM_NAME("AddConsoleAliasW", 3, "ExeName"); // LPWSTR
	ADD_PARAM_NAME("AddFontMemResourceEx", 1, "pFileView"); // PVOID
	ADD_PARAM_NAME("AddFontMemResourceEx", 2, "cjSize"); // DWORD
	ADD_PARAM_NAME("AddFontMemResourceEx", 3, "pvResrved"); // PVOID
	ADD_PARAM_NAME("AddFontMemResourceEx", 4, "pNumFonts"); // DWORD *
	ADD_PARAM_NAME("AddFontResourceA", 1, "lpszFilename"); // LPCSTR
	ADD_PARAM_NAME("AddFontResourceExA", 1, "name"); // LPCSTR
	ADD_PARAM_NAME("AddFontResourceExA", 2, "fl"); // DWORD
	ADD_PARAM_NAME("AddFontResourceExA", 3, "res"); // PVOID
	ADD_PARAM_NAME("AddFontResourceExW", 1, "name"); // LPCWSTR
	ADD_PARAM_NAME("AddFontResourceExW", 2, "fl"); // DWORD
	ADD_PARAM_NAME("AddFontResourceExW", 3, "res"); // PVOID
	ADD_PARAM_NAME("AddFontResourceW", 1, "lpszFilename"); // LPCWSTR
	ADD_PARAM_NAME("AddFormA", 1, "hPrinter"); // HANDLE
	ADD_PARAM_NAME("AddFormA", 2, "Level"); // DWORD
	ADD_PARAM_NAME("AddFormA", 3, "pForm"); // LPBYTE
	ADD_PARAM_NAME("AddFormW", 1, "hPrinter"); // HANDLE
	ADD_PARAM_NAME("AddFormW", 2, "Level"); // DWORD
	ADD_PARAM_NAME("AddFormW", 3, "pForm"); // LPBYTE
	ADD_PARAM_NAME("AddJobA", 1, "hPrinter"); // HANDLE
	ADD_PARAM_NAME("AddJobA", 2, "Level"); // DWORD
	ADD_PARAM_NAME("AddJobA", 3, "pData"); // LPBYTE
	ADD_PARAM_NAME("AddJobA", 4, "cbBuf"); // DWORD
	ADD_PARAM_NAME("AddJobA", 5, "pcbNeeded"); // LPDWORD
	ADD_PARAM_NAME("AddJobW", 1, "hPrinter"); // HANDLE
	ADD_PARAM_NAME("AddJobW", 2, "Level"); // DWORD
	ADD_PARAM_NAME("AddJobW", 3, "pData"); // LPBYTE
	ADD_PARAM_NAME("AddJobW", 4, "cbBuf"); // DWORD
	ADD_PARAM_NAME("AddJobW", 5, "pcbNeeded"); // LPDWORD
	ADD_PARAM_NAME("AddLocalAlternateComputerNameA", 1, "lpDnsFQHostname"); // LPCSTR
	ADD_PARAM_NAME("AddLocalAlternateComputerNameA", 2, "ulFlags"); // ULONG
	ADD_PARAM_NAME("AddLocalAlternateComputerNameW", 1, "lpDnsFQHostname"); // LPCWSTR
	ADD_PARAM_NAME("AddLocalAlternateComputerNameW", 2, "ulFlags"); // ULONG
	ADD_PARAM_NAME("AddMandatoryAce", 1, "pAcl"); // PACL
	ADD_PARAM_NAME("AddMandatoryAce", 2, "dwAceRevision"); // DWORD
	ADD_PARAM_NAME("AddMandatoryAce", 3, "AceFlags"); // DWORD
	ADD_PARAM_NAME("AddMandatoryAce", 4, "MandatoryPolicy"); // DWORD
	ADD_PARAM_NAME("AddMandatoryAce", 5, "pLabelSid"); // PSID
	ADD_PARAM_NAME("AddMonitorA", 1, "pName"); // LPSTR
	ADD_PARAM_NAME("AddMonitorA", 2, "Level"); // DWORD
	ADD_PARAM_NAME("AddMonitorA", 3, "pMonitorInfo"); // LPBYTE
	ADD_PARAM_NAME("AddMonitorW", 1, "pName"); // LPWSTR
	ADD_PARAM_NAME("AddMonitorW", 2, "Level"); // DWORD
	ADD_PARAM_NAME("AddMonitorW", 3, "pMonitorInfo"); // LPBYTE
	ADD_PARAM_NAME("AddPortA", 1, "pName"); // LPSTR
	ADD_PARAM_NAME("AddPortA", 2, "hWnd"); // HWND
	ADD_PARAM_NAME("AddPortA", 3, "pMonitorName"); // LPSTR
	ADD_PARAM_NAME("AddPortW", 1, "pName"); // LPWSTR
	ADD_PARAM_NAME("AddPortW", 2, "hWnd"); // HWND
	ADD_PARAM_NAME("AddPortW", 3, "pMonitorName"); // LPWSTR
	ADD_PARAM_NAME("AddPrintProcessorA", 1, "pName"); // LPSTR
	ADD_PARAM_NAME("AddPrintProcessorA", 2, "pEnvironment"); // LPSTR
	ADD_PARAM_NAME("AddPrintProcessorA", 3, "pPathName"); // LPSTR
	ADD_PARAM_NAME("AddPrintProcessorA", 4, "pPrintProcessorName"); // LPSTR
	ADD_PARAM_NAME("AddPrintProcessorW", 1, "pName"); // LPWSTR
	ADD_PARAM_NAME("AddPrintProcessorW", 2, "pEnvironment"); // LPWSTR
	ADD_PARAM_NAME("AddPrintProcessorW", 3, "pPathName"); // LPWSTR
	ADD_PARAM_NAME("AddPrintProcessorW", 4, "pPrintProcessorName"); // LPWSTR
	ADD_PARAM_NAME("AddPrintProvidorA", 1, "pName"); // LPSTR
	ADD_PARAM_NAME("AddPrintProvidorA", 2, "level"); // DWORD
	ADD_PARAM_NAME("AddPrintProvidorA", 3, "pProvidorInfo"); // LPBYTE
	ADD_PARAM_NAME("AddPrintProvidorW", 1, "pName"); // LPWSTR
	ADD_PARAM_NAME("AddPrintProvidorW", 2, "level"); // DWORD
	ADD_PARAM_NAME("AddPrintProvidorW", 3, "pProvidorInfo"); // LPBYTE
	ADD_PARAM_NAME("AddPrinterA", 1, "pName"); // LPSTR
	ADD_PARAM_NAME("AddPrinterA", 2, "Level"); // DWORD
	ADD_PARAM_NAME("AddPrinterA", 3, "pPrinter"); // LPBYTE
	ADD_PARAM_NAME("AddPrinterConnectionA", 1, "pName"); // LPSTR
	ADD_PARAM_NAME("AddPrinterConnectionW", 1, "pName"); // LPWSTR
	ADD_PARAM_NAME("AddPrinterDriverA", 1, "pName"); // LPSTR
	ADD_PARAM_NAME("AddPrinterDriverA", 2, "Level"); // DWORD
	ADD_PARAM_NAME("AddPrinterDriverA", 3, "pDriverInfo"); // LPBYTE
	ADD_PARAM_NAME("AddPrinterDriverExA", 1, "pName"); // LPSTR
	ADD_PARAM_NAME("AddPrinterDriverExA", 2, "Level"); // DWORD
	ADD_PARAM_NAME("AddPrinterDriverExA", 3, "pDriverInfo"); // LPBYTE
	ADD_PARAM_NAME("AddPrinterDriverExA", 4, "dwFileCopyFlags"); // DWORD
	ADD_PARAM_NAME("AddPrinterDriverExW", 1, "pName"); // LPWSTR
	ADD_PARAM_NAME("AddPrinterDriverExW", 2, "Level"); // DWORD
	ADD_PARAM_NAME("AddPrinterDriverExW", 3, "pDriverInfo"); // LPBYTE
	ADD_PARAM_NAME("AddPrinterDriverExW", 4, "dwFileCopyFlags"); // DWORD
	ADD_PARAM_NAME("AddPrinterDriverW", 1, "pName"); // LPWSTR
	ADD_PARAM_NAME("AddPrinterDriverW", 2, "Level"); // DWORD
	ADD_PARAM_NAME("AddPrinterDriverW", 3, "pDriverInfo"); // LPBYTE
	ADD_PARAM_NAME("AddPrinterW", 1, "pName"); // LPWSTR
	ADD_PARAM_NAME("AddPrinterW", 2, "Level"); // DWORD
	ADD_PARAM_NAME("AddPrinterW", 3, "pPrinter"); // LPBYTE
	ADD_PARAM_NAME("AddRefActCtx", 1, "hActCtx"); // HANDLE
	ADD_PARAM_NAME("AddSIDToBoundaryDescriptor", 1, "BoundaryDescriptor"); // HANDLE *
	ADD_PARAM_NAME("AddSIDToBoundaryDescriptor", 2, "RequiredSid"); // PSID
	ADD_PARAM_NAME("AddSecureMemoryCacheCallback", 1, "pfnCallBack"); // PSECURE_MEMORY_CACHE_CALLBACK
	ADD_PARAM_NAME("AddUsersToEncryptedFile", 1, "lpFileName"); // LPCWSTR
	ADD_PARAM_NAME("AddUsersToEncryptedFile", 2, "pUsers"); // PENCRYPTION_CERTIFICATE_LIST
	ADD_PARAM_NAME("AddVectoredContinueHandler", 1, "First"); // ULONG
	ADD_PARAM_NAME("AddVectoredContinueHandler", 2, "Handler"); // PVECTORED_EXCEPTION_HANDLER
	ADD_PARAM_NAME("AddVectoredExceptionHandler", 1, "First"); // ULONG
	ADD_PARAM_NAME("AddVectoredExceptionHandler", 2, "Handler"); // PVECTORED_EXCEPTION_HANDLER
	ADD_PARAM_NAME("AdjustTokenGroups", 1, "TokenHandle"); // HANDLE
	ADD_PARAM_NAME("AdjustTokenGroups", 2, "ResetToDefault"); // WINBOOL
	ADD_PARAM_NAME("AdjustTokenGroups", 3, "NewState"); // PTOKEN_GROUPS
	ADD_PARAM_NAME("AdjustTokenGroups", 4, "BufferLength"); // DWORD
	ADD_PARAM_NAME("AdjustTokenGroups", 5, "PreviousState"); // PTOKEN_GROUPS
	ADD_PARAM_NAME("AdjustTokenGroups", 6, "ReturnLength"); // PDWORD
	ADD_PARAM_NAME("AdjustTokenPrivileges", 1, "TokenHandle"); // HANDLE
	ADD_PARAM_NAME("AdjustTokenPrivileges", 2, "DisableAllPrivileges"); // WINBOOL
	ADD_PARAM_NAME("AdjustTokenPrivileges", 3, "NewState"); // PTOKEN_PRIVILEGES
	ADD_PARAM_NAME("AdjustTokenPrivileges", 4, "BufferLength"); // DWORD
	ADD_PARAM_NAME("AdjustTokenPrivileges", 5, "PreviousState"); // PTOKEN_PRIVILEGES
	ADD_PARAM_NAME("AdjustTokenPrivileges", 6, "ReturnLength"); // PDWORD
	ADD_PARAM_NAME("AdjustWindowRect", 1, "lpRect"); // LPRECT
	ADD_PARAM_NAME("AdjustWindowRect", 2, "dwStyle"); // DWORD
	ADD_PARAM_NAME("AdjustWindowRect", 3, "bMenu"); // WINBOOL
	ADD_PARAM_NAME("AdjustWindowRectEx", 1, "lpRect"); // LPRECT
	ADD_PARAM_NAME("AdjustWindowRectEx", 2, "dwStyle"); // DWORD
	ADD_PARAM_NAME("AdjustWindowRectEx", 3, "bMenu"); // WINBOOL
	ADD_PARAM_NAME("AdjustWindowRectEx", 4, "dwExStyle"); // DWORD
	ADD_PARAM_NAME("AdvancedDocumentPropertiesA", 1, "hWnd"); // HWND
	ADD_PARAM_NAME("AdvancedDocumentPropertiesA", 2, "hPrinter"); // HANDLE
	ADD_PARAM_NAME("AdvancedDocumentPropertiesA", 3, "pDeviceName"); // LPSTR
	ADD_PARAM_NAME("AdvancedDocumentPropertiesA", 4, "pDevModeOutput"); // PDEVMODEA
	ADD_PARAM_NAME("AdvancedDocumentPropertiesA", 5, "pDevModeInput"); // PDEVMODEA
	ADD_PARAM_NAME("AdvancedDocumentPropertiesW", 1, "hWnd"); // HWND
	ADD_PARAM_NAME("AdvancedDocumentPropertiesW", 2, "hPrinter"); // HANDLE
	ADD_PARAM_NAME("AdvancedDocumentPropertiesW", 3, "pDeviceName"); // LPWSTR
	ADD_PARAM_NAME("AdvancedDocumentPropertiesW", 4, "pDevModeOutput"); // PDEVMODEW
	ADD_PARAM_NAME("AdvancedDocumentPropertiesW", 5, "pDevModeInput"); // PDEVMODEW
	ADD_PARAM_NAME("AllocateAndInitializeSid", 1, "pIdentifierAuthority"); // PSID_IDENTIFIER_AUTHORITY
	ADD_PARAM_NAME("AllocateAndInitializeSid", 2, "nSubAuthorityCount"); // BYTE
	ADD_PARAM_NAME("AllocateAndInitializeSid", 3, "nSubAuthority0"); // DWORD
	ADD_PARAM_NAME("AllocateAndInitializeSid", 4, "nSubAuthority1"); // DWORD
	ADD_PARAM_NAME("AllocateAndInitializeSid", 5, "nSubAuthority2"); // DWORD
	ADD_PARAM_NAME("AllocateAndInitializeSid", 6, "nSubAuthority3"); // DWORD
	ADD_PARAM_NAME("AllocateAndInitializeSid", 7, "nSubAuthority4"); // DWORD
	ADD_PARAM_NAME("AllocateAndInitializeSid", 8, "nSubAuthority5"); // DWORD
	ADD_PARAM_NAME("AllocateAndInitializeSid", 9, "nSubAuthority6"); // DWORD
	ADD_PARAM_NAME("AllocateAndInitializeSid", 10, "nSubAuthority7"); // DWORD
	ADD_PARAM_NAME("AllocateAndInitializeSid", 11, "pSid"); // PSID *
	ADD_PARAM_NAME("AllocateLocallyUniqueId", 1, "Luid"); // PLUID
	ADD_PARAM_NAME("AllocateUserPhysicalPages", 1, "hProcess"); // HANDLE
	ADD_PARAM_NAME("AllocateUserPhysicalPages", 2, "NumberOfPages"); // PULONG_PTR
	ADD_PARAM_NAME("AllocateUserPhysicalPages", 3, "PageArray"); // PULONG_PTR
	ADD_PARAM_NAME("AllocateUserPhysicalPagesNuma", 1, "hProcess"); // HANDLE
	ADD_PARAM_NAME("AllocateUserPhysicalPagesNuma", 2, "NumberOfPages"); // PULONG_PTR
	ADD_PARAM_NAME("AllocateUserPhysicalPagesNuma", 3, "PageArray"); // PULONG_PTR
	ADD_PARAM_NAME("AllocateUserPhysicalPagesNuma", 4, "nndPreferred"); // DWORD
	ADD_PARAM_NAME("AllowSetForegroundWindow", 1, "dwProcessId"); // DWORD
	ADD_PARAM_NAME("AlphaBlend", 1, "hdcDest"); // HDC
	ADD_PARAM_NAME("AlphaBlend", 2, "xoriginDest"); // int
	ADD_PARAM_NAME("AlphaBlend", 3, "yoriginDest"); // int
	ADD_PARAM_NAME("AlphaBlend", 4, "wDest"); // int
	ADD_PARAM_NAME("AlphaBlend", 5, "hDest"); // int
	ADD_PARAM_NAME("AlphaBlend", 6, "hdcSrc"); // HDC
	ADD_PARAM_NAME("AlphaBlend", 7, "xoriginSrc"); // int
	ADD_PARAM_NAME("AlphaBlend", 8, "yoriginSrc"); // int
	ADD_PARAM_NAME("AlphaBlend", 9, "wSrc"); // int
	ADD_PARAM_NAME("AlphaBlend", 10, "hSrc"); // int
	ADD_PARAM_NAME("AlphaBlend", 11, "ftn"); // BLENDFUNCTION
	ADD_PARAM_NAME("AngleArc", 1, "hdc"); // HDC
	ADD_PARAM_NAME("AngleArc", 2, "x"); // int
	ADD_PARAM_NAME("AngleArc", 3, "y"); // int
	ADD_PARAM_NAME("AngleArc", 4, "r"); // DWORD
	ADD_PARAM_NAME("AngleArc", 5, "StartAngle"); // FLOAT
	ADD_PARAM_NAME("AngleArc", 6, "SweepAngle"); // FLOAT
	ADD_PARAM_NAME("AnimatePalette", 1, "hPal"); // HPALETTE
	ADD_PARAM_NAME("AnimatePalette", 2, "iStartIndex"); // UINT
	ADD_PARAM_NAME("AnimatePalette", 3, "cEntries"); // UINT
	ADD_PARAM_NAME("AnimatePalette", 4, "ppe"); // CONST PALETTEENTRY *
	ADD_PARAM_NAME("AnimateWindow", 1, "hWnd"); // HWND
	ADD_PARAM_NAME("AnimateWindow", 2, "dwTime"); // DWORD
	ADD_PARAM_NAME("AnimateWindow", 3, "dwFlags"); // DWORD
	ADD_PARAM_NAME("AppendMenuA", 1, "hMenu"); // HMENU
	ADD_PARAM_NAME("AppendMenuA", 2, "uFlags"); // UINT
	ADD_PARAM_NAME("AppendMenuA", 3, "uIDNewItem"); // UINT_PTR
	ADD_PARAM_NAME("AppendMenuA", 4, "lpNewItem"); // LPCSTR
	ADD_PARAM_NAME("AppendMenuW", 1, "hMenu"); // HMENU
	ADD_PARAM_NAME("AppendMenuW", 2, "uFlags"); // UINT
	ADD_PARAM_NAME("AppendMenuW", 3, "uIDNewItem"); // UINT_PTR
	ADD_PARAM_NAME("AppendMenuW", 4, "lpNewItem"); // LPCWSTR
	ADD_PARAM_NAME("AppendPrinterNotifyInfoData", 1, "pInfoDest"); // PPRINTER_NOTIFY_INFO
	ADD_PARAM_NAME("AppendPrinterNotifyInfoData", 2, "pInfoDataSrc"); // PPRINTER_NOTIFY_INFO_DATA
	ADD_PARAM_NAME("AppendPrinterNotifyInfoData", 3, "fdwFlags"); // DWORD
	ADD_PARAM_NAME("ApplicationRecoveryFinished", 1, "bSuccess"); // WINBOOL
	ADD_PARAM_NAME("ApplicationRecoveryInProgress", 1, "pbCanceled"); // PBOOL
	ADD_PARAM_NAME("Arc", 1, "hdc"); // HDC
	ADD_PARAM_NAME("Arc", 2, "x1"); // int
	ADD_PARAM_NAME("Arc", 3, "y1"); // int
	ADD_PARAM_NAME("Arc", 4, "x2"); // int
	ADD_PARAM_NAME("Arc", 5, "y2"); // int
	ADD_PARAM_NAME("Arc", 6, "x3"); // int
	ADD_PARAM_NAME("Arc", 7, "y3"); // int
	ADD_PARAM_NAME("Arc", 8, "x4"); // int
	ADD_PARAM_NAME("Arc", 9, "y4"); // int
	ADD_PARAM_NAME("ArcTo", 1, "hdc"); // HDC
	ADD_PARAM_NAME("ArcTo", 2, "left"); // int
	ADD_PARAM_NAME("ArcTo", 3, "top"); // int
	ADD_PARAM_NAME("ArcTo", 4, "right"); // int
	ADD_PARAM_NAME("ArcTo", 5, "bottom"); // int
	ADD_PARAM_NAME("ArcTo", 6, "xr1"); // int
	ADD_PARAM_NAME("ArcTo", 7, "yr1"); // int
	ADD_PARAM_NAME("ArcTo", 8, "xr2"); // int
	ADD_PARAM_NAME("ArcTo", 9, "yr2"); // int
	ADD_PARAM_NAME("AreAllAccessesGranted", 1, "GrantedAccess"); // DWORD
	ADD_PARAM_NAME("AreAllAccessesGranted", 2, "DesiredAccess"); // DWORD
	ADD_PARAM_NAME("AreAnyAccessesGranted", 1, "GrantedAccess"); // DWORD
	ADD_PARAM_NAME("AreAnyAccessesGranted", 2, "DesiredAccess"); // DWORD
	ADD_PARAM_NAME("ArrangeIconicWindows", 1, "hWnd"); // HWND
	ADD_PARAM_NAME("AssignProcessToJobObject", 1, "hJob"); // HANDLE
	ADD_PARAM_NAME("AssignProcessToJobObject", 2, "hProcess"); // HANDLE
	ADD_PARAM_NAME("AttachConsole", 1, "dwProcessId"); // DWORD
	ADD_PARAM_NAME("AttachThreadInput", 1, "idAttach"); // DWORD
	ADD_PARAM_NAME("AttachThreadInput", 2, "idAttachTo"); // DWORD
	ADD_PARAM_NAME("AttachThreadInput", 3, "fAttach"); // WINBOOL
}

} // namespace win_api
} // namespace semantics
} // namespace llvmir2hll
} // namespace retdec
